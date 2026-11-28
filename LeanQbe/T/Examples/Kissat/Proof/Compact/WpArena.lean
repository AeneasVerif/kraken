/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proof for `Kissat.Src.Compact.full_compact_arena`

Proves `Func.wp` against `fullCompactArenaSpec` (`Proof.Compact.Spec`) on flat `CanonicalEnv`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  bv_omega

private theorem bv32_shr1_nat_toNat (v : BitVec 32) :
    (v >>> (1 : Nat)).toNat = v.toNat / 2 := by
  bv_omega

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

private theorem fullArenaNextOff_mem_of_mem {ar : List (BitVec 32)} {alen r : Nat}
    (hr : r ∈ fullArenaScanRefs ar alen 0 alen)
    (hnext3 : fullArenaNextOff ar alen r + 3 ≤ alen) :
    fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen 0 alen := by
  have go : ∀ (fuel pos : Nat), alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel := by
    intro fuel; induction fuel with
    | zero => intro pos _ hmem; simp [fullArenaScanRefs] at hmem
    | succ f ih =>
      intro pos hfl hmem
      unfold fullArenaScanRefs at hmem ⊢; split at hmem
      · rename_i hle
        simp only [hle, ↓reduceIte, List.mem_cons] at hmem ⊢
        rcases hmem with rfl | hrest
        · right
          have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := r) hle
          have hf1 : 1 ≤ f := by omega
          obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
          unfold fullArenaScanRefs; simp [hnext3]
        · exact Or.inr (ih (fullArenaNextOff ar alen pos)
            (by have := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle; omega)
            hrest)
      · simp at hmem
  exact go alen 0 (by omega) hr

private theorem fullLastLearnedWf_of_cleared {s : FullState}
    (h : ∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FullLastLearnedWf s :=
  fun i hi => Or.inl (h i hi)

private def arenaKeepBinExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (h src dst fred irred redd nsrc arP : Val i64)
    (J1 : Cont [i64, i64, i64, i64, i64, i64])
    (Jl : Cont [i64, i64, i64, i64, i64]) : Expr Val Cont [i64] :=
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
  (Expr.jump J1 (Arg.var src, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd,
    Arg.imm 3, ()))) Blocks.nil) fun Js =>
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push"
    (Arg.var h, Arg.var ld_6, Arg.var p_37.fst, Arg.imm 0, Arg.imm 1, ()) fun p_40 =>
  Expr.jnz (Arg.var p_40.fst)
  (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push"
    (Arg.var h, Arg.var ld, Arg.var p_39.fst, Arg.imm 0, Arg.imm 1, ()) fun p_41 =>
   Expr.jnz (Arg.var p_41.fst)
   (Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 504, ())⟩ fun p_42 =>
    Expr.load i64 (Arg.var p_42.fst) fun ld =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var ld, Arg.imm 1, ())⟩ fun p_43 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 504, ())⟩ fun p =>
    Expr.store (Arg.var p_43.fst) (Arg.var p.fst)
    (Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ())))
   (Expr.jump Js.fst ()))
  (Expr.jump Js.fst ())

private def arenaKeepExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (h src dst fred irred redd nsrc arP : Val i64) (hdr : Val i32)
    (sat : Val .bool) (new_sz : Val i32)
    (J1 : Cont [i64, i64, i64, i64, i64, i64])
    (Jl : Cont [i64, i64, i64, i64, i64]) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var sat)
  (Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ()))
  (Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 0, ())⟩ fun p_27 =>
   Expr.jnz (Arg.var p_27.fst)
   (Expr.jump J1 (Arg.var src, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd,
      Arg.imm 2, ()))
   (Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 1, ())⟩ fun p_28 =>
    Expr.jnz (Arg.var p_28.fst)
    (Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ()))
    (Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 2, ())⟩ fun p_29 =>
     Expr.jnz (Arg.var p_29.fst)
     (arenaKeepBinExpr Val Cont h src dst fred irred redd nsrc arP J1 Jl)
     (Expr.let_ ⟨OpCode.mul i64, (Arg.var dst, Arg.imm 4, ())⟩ fun p =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
      Expr.let_ ⟨OpCode.or i32, (Arg.imm 8388608, Arg.imm 2097152, ())⟩ fun p_30 =>
      Expr.let_ ⟨OpCode.not i32, (Arg.var p_30.fst, ())⟩ fun p_31 =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var hdr, Arg.var p_31.fst, ())⟩ fun p_32 =>
      Expr.store (Arg.var p_32.fst) (Arg.var p.fst)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 1, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
       Expr.store (t := i32) (Arg.imm 2) (Arg.var p.fst)
       (Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 2, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
        Expr.store (Arg.var new_sz) (Arg.var p.fst)
        (Expr.group (sig := [[i64, i64, i64]]) (fun _Js =>
         Blocks.cons (fun p =>
         Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 3, ())⟩ fun p_33 =>
         Expr.let_ ⟨OpCode.zext 32 64, (Arg.var new_sz, ())⟩ fun p_34 =>
         Expr.let_ ⟨OpCode.add i64, (Arg.var p_33.fst, Arg.var p_34.fst, ())⟩ fun p_35 =>
         Expr.jump Jl (Arg.var nsrc, Arg.var p_35.fst, Arg.var p.fst, Arg.var p.snd.fst,
           Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Js =>
         Expr.let_ ⟨OpCode.and i32, (Arg.var hdr, Arg.imm 4194304, ())⟩ fun p =>
         Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p.fst, Arg.imm 0, ())⟩
           fun p =>
         Expr.jnz (Arg.var p.fst)
         (Expr.group (sig := [[i64]]) (fun _Js_3 =>
          Blocks.cons (fun p =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var redd, Arg.imm 1, ())⟩ fun p_33 =>
          Expr.jump Js.fst (Arg.var p.fst, Arg.var irred, Arg.var p_33.fst, ()))
            Blocks.nil) fun Js =>
          Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            (Arg.var fred, Arg.imm 4294967295, ())⟩ fun p =>
          Expr.jnz (Arg.var p.fst)
          (Expr.jump Js.fst (Arg.var dst, ()))
          (Expr.jump Js.fst (Arg.var fred, ())))
         (Expr.let_ ⟨OpCode.add i64, (Arg.var irred, Arg.imm 1, ())⟩ fun p =>
          Expr.jump Js.fst (Arg.var fred, Arg.var p.fst, Arg.var redd, ())))))))))

private def arenaInnerExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (src dst nlits arP valsP mapP : Val i64) (old_sz : Val i32)
    (Ji : Cont [.bool, i32, i32]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i32]]) (fun Js_2 =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.snd.fst, Arg.var old_sz, ())⟩
    fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var src, Arg.imm 3, ())⟩ fun p_27 =>
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
   Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_32.fst, Arg.var nlits, ())⟩
     fun p_33 =>
   Expr.jnz (Arg.var p_33.fst)
   (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld_6, ())⟩ fun p_34 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var valsP, Arg.var p_34.fst, ())⟩ fun p_35 =>
    Expr.load i8 (Arg.var p_35.fst) fun ld_7 =>
    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_36 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld_7, ())⟩ fun p_37 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_36.fst, ())⟩ fun p_38 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl, (Arg.var p_37.fst, Arg.var p_38.fst, ())⟩
      fun p_39 =>
    Expr.jnz (Arg.var p_39.fst)
    (Expr.jump Ji (Arg.imm true, Arg.var p.fst, Arg.var p.snd.fst, ()))
    (Expr.group (sig := [[.bool, i32]]) (fun _Js =>
     Blocks.cons (fun p =>
     Expr.jump Js_3.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js_4 =>
     Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_40 =>
     Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld_7, ())⟩ fun p_41 =>
     Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_40.fst, ())⟩ fun p_42 =>
     Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
       (Arg.var p_41.fst, Arg.var p_42.fst, ())⟩ fun p_43 =>
     Expr.jnz (Arg.var p_43.fst)
     (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld_6, Arg.imm 1, ())⟩ fun p_44 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_44.fst, ())⟩ fun p_45 =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var p_45.fst, Arg.imm 4, ())⟩ fun p_46 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_46.fst, ())⟩ fun p_47 =>
      Expr.load i32 (Arg.var p_47.fst) fun ld_8 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
        (Arg.var ld_8, Arg.imm 4294967295, ())⟩ fun p_48 =>
      Expr.jnz (Arg.var p_48.fst)
      (Expr.jump Ji (Arg.imm true, Arg.var p.fst, Arg.var p.snd.fst, ()))
      (Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 3, ())⟩ fun p_49 =>
       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_50 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var p_49.fst, Arg.var p_50.fst, ())⟩ fun p_51 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p_51.fst, Arg.imm 4, ())⟩ fun p_52 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p_52.fst, ())⟩ fun p_53 =>
       Expr.let_ ⟨OpCode.shl i32, (Arg.var ld_8, Arg.imm 1, ())⟩ fun p_54 =>
       Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 1, ())⟩ fun p_55 =>
       Expr.let_ ⟨OpCode.or i32, (Arg.var p_54.fst, Arg.var p_55.fst, ())⟩ fun p_56 =>
       Expr.store (Arg.var p_56.fst) (Arg.var p_53.fst)
       (Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
        Expr.jump Js_4.fst (Arg.imm false, Arg.var p.fst, ()))))
     (Expr.jump Js_4.fst (Arg.imm false, Arg.var p.fst, ()))))
   (Expr.jump Js_3.fst (Arg.imm false, Arg.var p.fst, ())))
  (Expr.jump Ji (Arg.imm false, Arg.var p.fst, Arg.var p.snd.fst, ()))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private theorem full_compact_arena_keep_bin {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {J1 : Cont [i64, i64, i64, i64, i64, i64]}
    {Jl : Cont [i64, i64, i64, i64, i64]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ncv : Nat}
    {s sI : FullState} {kI : FullCoreState} {R : Mem 64 → Prop}
    {arI wvecL wstkL wsL : List (BitVec 32)} {wlenL : Nat}
    {wuL nbL oomL src dst fred irred redd nsrc : BitVec 64}
    {old_sz new_sz : BitVec 32} {nsrc_nat : Nat} {mI : Mem 64}
    (hkI : kI = { s.core with arena := arI, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                                wusable := wuL, num_binary := nbL, oom := oomL })
    (hsI : sI = { s with core := kI, scratch := { s.scratch with wsort := wsL } })
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hncv_le : ncv ≤ s.core.cur_vars) (hd_le : dst.toNat ≤ src.toNat)
    (hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hnsrc_bounds : src.toNat + 3 + old_sz.toNat ≤ nsrc_nat ∧ nsrc_nat ≤ s.core.arena_len ∧
      (nsrc_nat = s.core.arena_len ∨ nsrc_nat + 3 ≤ s.core.arena_len))
    (hnsrc_to : (BitVec.ofNat 64 nsrc_nat).toNat = nsrc_nat)
    (hnsrc64 : nsrc = BitVec.ofNat 64 nsrc_nat)
    (hnsrc_mem : nsrc_nat = s.core.arena_len ∨ nsrc_nat ∈ fullArenaClauseRefsCore s.core)
    (hckI : FullCoreState.LengthsOk c kI) (hws_ok : FullScratch.LengthsOk c s.scratch)
    (hwsL_len : wsL.length = 2 * c.max_vars)
    (har_tailI : ∀ j, nsrc_nat ≤ j → j < s.core.arena_len → arI[j]? = s.core.arena[j]?)
    (hpreI : CompactArenaPrefix c ncv s.scratch.work_stk2 F_cur arI dst.toNat)
    (hbinI : CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur kI)
    (hns2 : new_sz.toNat = 2) (hns_le : new_sz.toNat ≤ old_sz.toNat)
    (hkl_lt : ∀ j < new_sz.toNat,
      (arI[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * ncv)
    (hkl_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat).map
        (compactUnmapLit s.scratch.work_stk2))))
    (hmI : (FullMem c sI ⋆ R) mI)
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
    wp Γ Q X (arenaKeepBinExpr Val Cont c.hdr src dst fred irred redd nsrc c.pArena J1 Jl)
      mI := by
  unfold arenaKeepBinExpr
  subst hkI hsI
  let inv := s.scratch.work_stk2
  let kI : FullCoreState :=
    { s.core with arena := arI, wvec := wvecL, wstk := wstkL, wlen := wlenL, wusable := wuL,
                  num_binary := nbL, oom := oomL }
  let sI : FullState := { s with core := kI, scratch := { s.scratch with wsort := wsL } }
  have har_len : arI.length = c.arena_cap := hckI.arena_len_arr
  have hmax_lt := c.hmaxv; have hcap_lt := c.harena; unfold dimacsBound at hmax_lt hcap_lt
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
  have hkept2 : ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat =
      [l0.toNat, l1.toNat] := by
    rw [hns2]
    have ha := cmp_drop_take_succ hd3_lt (off := dst.toNat + 3) (n := 0)
    have hb := cmp_drop_take_succ hd4_lt (off := dst.toNat + 3) (n := 1)
    simp only [Nat.add_zero, List.take_zero, List.nil_append] at ha
    rw [hb, ha]; rfl
  rw [hkept2] at hkl_ent
  have hkl_ent10 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [compactUnmapLit inv l1.toNat, compactUnmapLit inv l0.toNat]) := by
    refine cmp_entails_of_mem_or_false hkl_ent fun x hx => ?_
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨a, rfl | rfl, rfl⟩ := hx
    · exact Or.inl (by simp [inv])
    · exact Or.inl (by simp [inv])
  have hbw0 := cmp_bv32_bin_word_props (show l1.toNat < 0x7FFFFFFF by omega)
  have hbw1 := cmp_bv32_bin_word_props (show l0.toNat < 0x7FFFFFFF by omega)
  have hd3_nat : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := cmp_bv64_add3 (by omega)
  have hd4_nat : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4 := cmp_bv64_add4 (by omega)
  c0_hsteps; c0_hcall hpush
  refine ⟨c, sI, R, rfl, ⟨hckI, { hws_ok with wsort_len := hwsL_len }⟩,
    hbinI.layout, fun _ => by simp only [hd4_nat]; exact hbw0.2.1,
    fun hc2 => absurd hc2 (by decide), hmI,
    fun ok0 wvec0 wstk0 wlen0 wu0 ws0 m0 hlen0 hlay0 hoth0 hok0_t hok0_f hm0 => ?_⟩
  clear hmI
  dsimp only at hoth0 hok0_t hok0_f
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
  c0_hsplit
  · let sI0 : FullState :=
      { sI with core := { kI with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := wu0 },
                scratch := { sI.scratch with wsort := ws0 } }
    c0_hsteps; c0_hcall hpush
    refine ⟨c, sI0, R, rfl, hlen0, hbin0'.layout,
      fun _ => by simp only [hd3_nat]; exact hbw1.2.1,
      fun hc2 => absurd hc2 (by decide), hm0,
      fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1_t hok1_f hm1 => ?_⟩
    clear hm0
    dsimp only at hoth1 hok1_t hok1_f
    have hl1_bv_eq :
        (arI[(dst + (4 : BitVec 64)).toNat]'(by rw [hd4_nat]; exact hd4_lt)).toNat =
          l1.toNat := congrArg BitVec.toNat (by simp only [hd4_nat]; rfl)
    have hbin1' : CompactUnmapBinsOk ncv inv F_cur
        { sI0.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1 } := by
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
    c0_hsplit
    · c0_hsteps
      refine hLoopL (nsrc, dst, fred, irred, redd, ()) _
        (by dsimp only; rw [hnsrc64, hnsrc_to]; omega)
        ⟨by dsimp only; rw [hnsrc64, hnsrc_to]; omega,
         by dsimp only; rw [hnsrc64, hnsrc_to]; omega,
         by dsimp only; rw [hnsrc64, hnsrc_to]; exact hnsrc_mem,
         arI, wvec1, wstk1, wlen1, wu1, nbL + 1#64, oomL, ws1,
         { hlen1.core_ok with cur_vars_le := hckI.cur_vars_le },
         hlen1.scratch_ok.wsort_len,
         by dsimp only; rw [hnsrc64, hnsrc_to]; exact har_tailI, hpreI,
         ⟨⟨hbin1'.layout.bounds, hbin1'.layout.pos_off, hbin1'.layout.disjoint,
            hbin1'.layout.no_sentinel⟩, hbin1'.empty_hi, fun l hl => by
            have hs0 := hbin1'.slices l hl
            unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
            exact hs0.relocate (fun _ _ => by rfl)⟩,
         ?_⟩
      assumption
    · c0_hsteps
      refine hJ1 (src, dst, fred, irred, redd, 3#64, ()) _
        ⟨by dsimp only; omega, Or.inr (Or.inr rfl),
         fun h => by dsimp only at h; exact absurd h (by decide),
         arI, wvec1, wstk1, wlen1, wu1, nbL, 1#64, ws1, { hlen1.core_ok with },
         hlen1.scratch_ok.wsort_len, fun _ => rfl, hpreI,
         ⟨⟨hbin1'.layout.bounds, hbin1'.layout.pos_off, hbin1'.layout.disjoint,
            hbin1'.layout.no_sentinel⟩, hbin1'.empty_hi, fun l hl => by
            have hs0 := hbin1'.slices l hl
            unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
            exact hs0.relocate (fun _ _ => by rfl)⟩,
         ?_⟩
      assumption
  · c0_hsteps
    refine hJ1 (src, dst, fred, irred, redd, 3#64, ()) _
      ⟨by dsimp only; omega, Or.inr (Or.inr rfl),
       fun h => by dsimp only at h; exact absurd h (by decide),
       arI, wvec0, wstk0, wlen0, wu0, nbL, 1#64, ws0, { hlen0.core_ok with },
       hlen0.scratch_ok.wsort_len, fun _ => rfl, hpreI,
       ⟨⟨hbin0'.layout.bounds, hbin0'.layout.pos_off, hbin0'.layout.disjoint,
          hbin0'.layout.no_sentinel⟩, hbin0'.empty_hi, fun l hl => by
          have hs0 := hbin0'.slices l hl
          unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
          exact hs0.relocate (fun _ _ => by rfl)⟩,
       ?_⟩
    assumption

private theorem full_compact_arena_keep {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hpush : Γ.Has "full_watch_push" fullWatchPushSpec)
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
    (_hmax_lt : c.max_vars < 2 * 2 ^ 28) (har_cap_lt : c.arena_cap < 2 * 2 ^ 28)
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
  c0_hsplit
  · c0_hsteps
    exact hLoopL (nsrc, dst, fred, irred, redd, ()) mI
      (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
      ⟨by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem,
       arI, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckI, hwsL_len,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailI, hpreI, hbinI, hmI⟩
  · have hsat_f : sat = false := by c0_bound
    obtain ⟨hkl_lt, hkl_nd, hkl_ent⟩ := hsatI hsat_f
    c0_hsplit
    · have hns0 : new_sz.toNat = 0 := by c0_bound
      have hnil : ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat = [] := by
        simp [hns0]
      rw [hnil, List.map_nil] at hkl_ent
      have hunsat : F0.Unsat := hext_u (cmp_unsat_of_entails_nil hkl_ent)
      c0_hsteps
      exact hJ1 (src, dst, fred, irred, redd, 2#64, ()) mI
        ⟨by dsimp only; omega, Or.inr (Or.inl rfl), fun _ => hunsat, arI, wvecL, wstkL, wlenL,
         wuL, nbL, oomL, wsL, hckI, hwsL_len,
         fun h => by dsimp only at h; exact absurd h (by decide), hpreI, hbinI, hmI⟩
    · c0_hsplit
      · c0_hsteps
        exact hLoopL (nsrc, dst, fred, irred, redd, ()) mI
          (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
          ⟨by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem,
           arI, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckI, hwsL_len,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailI, hpreI, hbinI, hmI⟩
      · c0_hsplit
        · exact full_compact_arena_keep_bin hpush rfl rfl hcv_le hal_le hncv_le hd_le hfit_src
            hnsrc_bounds hnsrc_to (by rw [hnsrc_eq, hnsrc64]) hnsrc_mem hckI hws_ok hwsL_len
            har_tailI hpreI hbinI (by c0_bound) hns_le hkl_lt hkl_ent hmI hJ1 hLoopL
        · have hns3 : 3 ≤ new_sz.toNat := by c0_bound
          have hdst_lt_cap : dst.toNat + 3 + new_sz.toNat ≤ s.core.arena_len := by omega
          have hd0_lt : dst.toNat < arI.length := by omega
          have hd1_lt : dst.toNat + 1 < arI.length := by omega
          have hd2_lt : dst.toNat + 2 < arI.length := by omega
          have hd3_eq : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
              dst.toNat + 3 + new_sz.toNat := cmp_bv64_add3_zext_toNat (by omega)
          let arW :=
            ((arI.set dst.toNat (hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
              (dst.toNat + 1) 2#32).set (dst.toNat + 2) new_sz
          have hclear := cmp_bv32_clear_shrk_rsn hdr hng
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
          have hd1_nat : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1 :=
            cmp_bv64_add1 (by omega)
          have hd2_nat : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2 :=
            cmp_bv64_add2 (by omega)
          have harW_eq : arW =
              ((arI.set dst.toNat (hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
                (dst + (1 : BitVec 64)).toNat 2#32).set
                (dst + (2 : BitVec 64)).toNat new_sz := by
            dsimp only [arW]; rw [hd1_nat, hd2_nat]
          c0_hsteps
          · exact hcontW dst irred (redd + 1#64) _ (by rw [harW_eq]; assumption)
          · exact hcontW fred irred (redd + 1#64) _ (by rw [harW_eq]; assumption)
          · exact hcontW fred (irred + 1#64) redd _ (by rw [harW_eq]; assumption)

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
  · c0_hsteps
    refine hLoopI (0#32, 0#32, ()) mL ⟨Nat.zero_le _, Nat.zero_le _, arL, hckL.arena_len_arr,
      fun _ _ _ => rfl, ?_, hmL⟩
    refine ⟨fun j hj => by simp at hj, ?_, ?_, ?_⟩ <;> simp
  · rintro Ji' ⟨new_sz, i, ⟨⟩⟩ mI ⟨hi_le, hns_le, arI, harI, hpresI, hsatI, hmI⟩ hLoopI
    c0_hsplit
    · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
      have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := cmp_bv32_add1 (by omega)
      have hsi_eq : (src + (3 : BitVec 64) + i.setWidth 64).toNat =
          src.toNat + 3 + i.toNat := cmp_bv64_add3_zext_toNat (by omega)
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
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · have hlit_lt64 : lit.toNat < 2 * old_cv.toNat := by c0_bound
        have hlit_vals : lit.toNat < s.core.vals.length := by omega
        have hlit_ws1 : (lit >>> (1 : Nat)).toNat < s.scratch.work_stk1.length := by
          rw [bv32_shr1_nat_toNat]; omega
        have hlit_bv64 : (BitVec.setWidth 64
            (arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
              rw [hsi_eq]; exact hsi_lt))).toNat < kCore.vals.length := by
          rw [zext_toNat _ (by decide)]; simp only [hsi_eq]; exact hlit_vals
        have hws1_bv64 : (BitVec.setWidth 64
            ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
              rw [hsi_eq]; exact hsi_lt)) >>> (1 : Nat))).toNat <
            kL.scratch.work_stk1.length := by
          rw [zext_toNat _ (by decide)]; simp only [hsi_eq]; exact hlit_ws1
        c0_hsteps
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
                  rw [hidx_s]; exact hsi_lt)) >>> (1 : Nat)).toNat]'(by
                  simp only [hidx_s]; exact hlit_ws1)) ≠ 0xFFFFFFFF#32 := by
              c0_bound
            have hneq : (s.scratch.work_stk1[(lit >>> (1 : Nat)).toNat]'(by omega)) ≠
                0xFFFFFFFF#32 := by simpa only [hidx_s] using hneq_raw
            simp only [bv32_shr1_nat_toNat] at hneq; exact hneq (Option.some.inj heq)
          rcases hbij.map_ok (lit.toNat / 2) (by omega) with
              hff | ⟨nv, hnv, _, _, hm_l, hi_l⟩
          · exact absurd hff hmap_ne
          · have hnv30 : nv < 2 ^ 30 := by omega
            have hnv_eq : (s.scratch.work_stk1[(lit >>> (1 : Nat)).toNat]'(by omega)) =
                BitVec.ofNat 32 nv := by
              rw [List.getElem?_eq_getElem
                (by omega : lit.toNat / 2 < s.scratch.work_stk1.length)] at hm_l
              simp only [bv32_shr1_nat_toNat]; exact Option.some.inj hm_l
            have hpack := cmp_bv32_lit_pack hnv30 lit
            let lnew : BitVec 32 := (BitVec.ofNat 32 nv <<< (1 : Nat)) ||| (lit &&& 1#32)
            have hd_lt : dst.toNat + 3 + new_sz.toNat < arI.length := by omega
            have hns1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1 :=
              cmp_bv32_add1 (by omega)
            have hi1_val : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
              cmp_bv32_add1 (by omega)
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
                have hdt := cmp_drop_take_succ (xs := arI') (off := dst.toNat + 3)
                  (n := new_sz.toNat) (by simp [arI', harI]; omega)
                rw [hdt, hlen_pre, List.map_append, List.map_singleton]
                congr 2; dsimp only [arI']; exact congrArg BitVec.toNat (List.getElem_set_self _)
              have hinv_new :
                  (inv[lnew.toNat / 2]?.getD 0#32).toNat = lit.toNat / 2 := by
                rw [show lnew.toNat = 2 * nv + lit.toNat % 2 from hpack,
                  show (2 * nv + lit.toNat % 2) / 2 = nv by omega,
                  hi_l, Option.getD_some, bv32_ofNat_toNat (by omega)]
              refine ⟨fun j hj => ?_, ?_, fun x hx => ?_, fun l hl => ?_⟩
              · rw [hns1_eq] at hj
                by_cases hjn : j = new_sz.toNat
                · subst hjn; dsimp only [arI']
                  rw [List.getElem?_set_self (by simp [harI]; omega), Option.getD_some]
                  change lnew.toNat < 2 * ncv
                  rw [show lnew.toNat = 2 * nv + lit.toNat % 2 from hpack]; omega
                · dsimp only [arI']
                  rw [List.getElem?_set_ne (by omega)]; exact hjl j (by omega)
              · rw [hkept']
                apply nodup_unmap_kept (fun x hx => (hcovK x hx).1) hndK
                  (by
                    change lnew.toNat / 2 < ncv
                    rw [show lnew.toNat = 2 * nv + lit.toNat % 2 from hpack]; omega)
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
                · refine ⟨by
                      change lnew.toNat / 2 < ncv
                      rw [show lnew.toNat = 2 * nv + lit.toNat % 2 from hpack]; omega, ?_⟩
                  rw [hinv_new, hi1_val, htake_succ, List.map_append, List.map_singleton]
                  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [hi1_val, htake_succ, List.mem_append, List.mem_singleton] at hl
                rcases hl with hl | rfl
                · rcases hsubK l hl with hin | hunit
                  · rw [hkept', List.map_append]; exact Or.inl (List.mem_append_left _ hin)
                  · exact Or.inr hunit
                · left; rw [hkept', List.map_append, List.map_singleton]
                  refine List.mem_append_right _ (List.mem_singleton.mpr ?_)
                  have hum := compactUnmapLit_pair (inv := inv) (nv := nv) (ov := lit.toNat / 2)
                    (p := lit.toNat % 2)
                    (by rw [hi_l, Option.getD_some, bv32_ofNat_toNat (by omega)])
                    (Nat.mod_lt _ (by decide))
                  change lit.toNat = compactUnmapLit inv lnew.toNat
                  rw [show lnew.toNat = 2 * nv + lit.toNat % 2 from hpack, hum]; omega
            · have hd_eq : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
                  dst.toNat + 3 + new_sz.toNat := cmp_bv64_add3_zext_toNat (by omega)
              have hnv_zext :
                  (kL.scratch.work_stk1[(BitVec.setWidth 64
                    ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                      rw [hsi_eq]; exact hsi_lt)) >>> (1 : Nat))).toNat]'(
                      hws1_bv64)) = BitVec.ofNat 32 nv := by
                apply Option.some.inj
                have hg := List.getElem?_eq_getElem hws1_bv64
                change some (kL.scratch.work_stk1[(BitVec.setWidth 64
                  ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                    rw [hsi_eq]; exact hsi_lt)) >>> (1 : Nat))).toNat]'hws1_bv64) =
                  some (BitVec.ofNat 32 nv)
                rw [← hg, zext_toNat _ (by decide)]; simp only [hsi_eq]
                rw [bv32_shr1_nat_toNat]; exact hm_l
              have har_rhs : arI' =
                  arI.set (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat
                    ((kL.scratch.work_stk1[(BitVec.setWidth 64
                      ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                        rw [hsi_eq]; exact hsi_lt)) >>> (1 : Nat))).toNat]'(
                        hws1_bv64) <<< (1 : Nat)) |||
                      ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                        rw [hsi_eq]; exact hsi_lt)) &&& (1 : BitVec 32))) := by
                dsimp only [arI', lnew]; rw [hd_eq, hnv_zext]; simp only [hsi_eq]; rfl
              rw [har_rhs]; assumption
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
          c0_hsteps
          have hi1_val : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := cmp_bv32_add1 (by omega)
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
      c0_hsteps
      refine hJi (false, new_sz, i, ()) mI ⟨hi_eq ▸ hns_le, arI, harI, hpresI, fun _ => ?_, hmI⟩
      obtain ⟨hjl, hndK, _, hsubK⟩ := hsatI
      have htake_all : olits.take i.toNat = olits := by
        rw [hi_eq, ← hol_len]; exact List.take_length
      rw [htake_all] at hsubK
      refine ⟨hjl, hndK, compactArena_entails_kept hent_ol fun l hl => ?_⟩
      rcases hsubK l hl with hin | ⟨_, hunit⟩
      · exact Or.inl hin
      · exact Or.inr hunit

public section

/-- Canonical WP proof for `full_compact_arena` (`Proof.Compact.Spec.compactArenaSpec`). -/
theorem full_compact_arena_wp (Γ : Env)
    (hnext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hpush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ a m Q X, compactArenaSpec a m Q X →
      Func.wp Γ full_compact_arena_body a m Q X := by
  rintro ⟨h, old_cv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨F0, F_cur, ncv⟩, R, rfl, hlen,
    ⟨hext_s, har_inv, hnd, hdm, hcl0, hold, hncv_le, hbij, hdom, hfent, hbin0⟩, hm, hQ0⟩ :=
    FullContract.elim hs
  let hQ : ∀ ast ar' al' fred' ni' nr' wvec' wstk' wlen' wu' nb' oom' ll' ws' m',
      let s' : FullState :=
        { core := { s.core with arena := ar', arena_len := al', arena_garbage := 0#64,
                                first_reducible := fred', num_irred := ni', num_redundant := nr',
                                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                num_binary := nb', oom := oom' }
          scratch := { s.scratch with last_learned := ll', wsort := ws' } }
      s'.LengthsOk c → (ast = 0#64 ∨ ast = 2#64 ∨ ast = 3#64) → (ast = 2#64 → F0.Unsat) →
      (ast = 3#64 → oom' = 1#64) → CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s'.core →
      CompactArenaOk ncv s.scratch.work_stk2 F_cur s'.core → FullLastLearnedWf s' →
      (FullMem c s' ⋆ R) m' → Q (ast, ()) m' :=
    fun ast ar' al' fred' ni' nr' wvec' wstk' wlen' wu' nb' oom' ll' ws' m'
      hlen' hret h2 h3 hbin' har' hll' hm' =>
      hQ0 (ast, ()) _ m' hlen' ⟨rfl, rfl, hret, h2, h3, hbin', har', hll'⟩ hm'
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
  unfold Func.wp full_compact_arena_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_join_group (ts := [i64, i64, i64, i64, i64, i64])
    (fun xs mE =>
      let dst := xs.2.1
      let fred := xs.2.2.1
      let irred := xs.2.2.2.1
      let redd := xs.2.2.2.2.1
      let status := xs.2.2.2.2.2.1
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
    dsimp only at hd_le hst_ok hst2 hst3 hpreE
    c0_hsteps
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
    · c0_hsteps
      exact hLoopLi (0#64, ()) _ ⟨Nat.zero_le _, s.scratch.last_learned, hll_len,
        fun _ h => by simp at h, by assumption⟩
    · rintro Jli ⟨li, ⟨⟩⟩ mLi ⟨hli_le, llL, hllL, hallL, hmLi⟩ hLoopLi
      c0_hsplit
      · have hli_lt : li.toNat < 16 := by c0_bound
        have hli1_eq : (li + (1 : BitVec 64)).toNat = li.toNat + 1 :=
          cmp_bv64_add1 (by omega)
        c0_hsteps
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
        have harF : CompactArenaOk ncv inv F_cur sF.core :=
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
        c0_hsteps
        exact hQ status arE dst.toNat fred irred redd wvecE wstkE wlenE wuE nbE oomE llL wsE mLi
          hckF hst_ok hst2 hst3 hbinF harF hllF hmLi
  · intro J1 hJ1
    c0_hsteps
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
    · c0_hsteps
      exact hLoopL (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, ()) m
        ⟨Nat.zero_le _, Nat.zero_le _,
         (by rcases hsrc0 with hz | hr; exact Or.inl hz.symm; exact Or.inr hr),
         s.core.arena, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
         s.core.num_binary, s.core.oom, s.scratch.wsort, hck0, hlen.scratch_ok.wsort_len,
         fun _ _ _ => rfl, compactArenaPrefix_empty _ _ _ _ _, hbin0, hm⟩
    · rintro Jl ⟨src, dst, fred, irred, redd, ⟨⟩⟩ mL
        ⟨hd_le, hsrc_le, hsrc_ok, arL, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL,
         hckL, hwsL_len, har_tail, hpreL, hbinL, hmL⟩ hLoopL
      let kL : FullCoreState :=
        { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                      wusable := wuL, num_binary := nbL, oom := oomL }
      let sL : FullState := { s with core := kL, scratch := { s.scratch with wsort := wsL } }
      c0_hsplit
      · have hsrc_lt : src.toNat < s.core.arena_len := by c0_bound
        have hsrc_ref : src.toNat ∈ fullArenaClauseRefsCore s.core := by
          rcases hsrc_ok with h | h
          · omega
          · exact h
        have hwf := har_inv.refs_wf src.toNat hsrc_ref
        c0_hsplit
        · exfalso
          have h3lt : s.core.arena_len < (src + (3 : BitVec 64)).toNat := by c0_bound
          have h3eq : (src + (3 : BitVec 64)).toNat = src.toNat + 3 :=
            cmp_bv64_add3 (by omega)
          have := hwf.1; omega
        · have hsrc3_le : src.toNat + 3 ≤ s.core.arena_len := by c0_bound
          have hsrc2_eq : (src + (2 : BitVec 64)).toNat = src.toNat + 2 :=
            cmp_bv64_add2 (by omega)
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
          c0_hsteps; c0_hcall hnext
          refine ⟨c, sL, R, rfl, ⟨hckL, { hlen.scratch_ok with wsort_len := hwsL_len }⟩, hmL, ?_⟩
          dsimp only
          rw [hsrc32_eq, hnxt_eq, hhdr_arL, har_src2]
          c0_hsplit
          · c0_hsteps
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
            c0_hsplit <;> first
              | (exfalso; have h2 : old_sz.toNat < 3 := by c0_bound
                 have hsz3 : 3 ≤ old_sz.toNat := hosz_eq ▸ hwf.2.1; omega)
              | skip
            c0_hsplit <;> first
              | (exfalso
                 have h3 :
                     s.core.arena_len < (src + (3 : BitVec 64) + old_sz.setWidth 64).toNat := by
                   c0_bound
                 have hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len := by
                   have := hosz_eq ▸ hwf.2.2.1; omega
                 have hfit_64 : src.toNat + 3 + old_sz.toNat < 2 ^ 64 := by omega
                 rw [cmp_bv64_add3_zext_toNat hfit_64] at h3; omega)
              | skip
            have hsz3 : 3 ≤ old_sz.toNat := hosz_eq ▸ hwf.2.1
            have hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len := by
              have := hosz_eq ▸ hwf.2.2.1; omega
            have hfit_64 : src.toNat + 3 + old_sz.toNat < 2 ^ 64 := by omega
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
            c0_hsteps_nogrp
            refine LeanQbe.T.wp_join_group (ts := [.bool, i32, i32])
              (fun xs mI =>
                let sat := xs.1
                let new_sz := xs.2.1
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
              dsimp only at hns_le hsatI
              exact full_compact_arena_keep hpush (c := c) (s := s) (sL := sL) (kCore := kL)
                rfl rfl rfl hext_s.2 hcv_le hal_le hmax_lt har_cap_lt
                (hold ▸ hncv_le) hd_le hsrc_lt hsz3 hfit_src hnsrc_bounds hnsrc_to hnsrc64
                hnsrc_mem hng hckL hlen.scratch_ok hwsL_len
                (fun j hj1 hj2 => har_tail j (by omega) hj2) hpreL hbinL hns_le harI hpresI
                hsatI hmI hJ1 hLoopL
            · intro Ji hJi
              clear hm hbin0
              refine full_compact_arena_inner (c := c) (s := s) (kL := sL) (kCore := kL) rfl rfl
                hckL hcv_le hal_le hv_len hws1_len hmax_lt har_cap_lt hold ?_ hncv_le hbij
                hdom hfent hd_le hfit_src hol_len hol_mem hol_lt hol_nd
                (har_inv.entails src.toNat hsrc_ref hgarb_f)
                (fun j hj1 hj2 => har_tail j (by omega) (by omega)) hmL hJi
              simpa [bv_c0] using hnlits_eq
      · have hsrc_eq : src.toNat = s.core.arena_len := by c0_bound
        c0_hsteps
        exact hJ1 (src, dst, fred, irred, redd, 0#64, ()) mL
          ⟨by dsimp only; omega, Or.inl rfl,
           (fun h => by dsimp only at h; exact absurd h (by decide)),
           arL, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckL, hwsL_len,
           (fun h => by dsimp only at h; exact absurd h (by decide)), hpreL, hbinL, hmL⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
