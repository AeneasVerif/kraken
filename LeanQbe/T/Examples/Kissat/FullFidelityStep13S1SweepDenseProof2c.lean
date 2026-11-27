/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2b
import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls
import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1b
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 2c (`full_m6_els_lit` & `full_m6_dense_els`)

Parametric `(Γ : Env)` proofs (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_m6_els_lit_s13_wp` (`step13ElsLitSpec`)
2. `full_m6_dense_els_s13_wp` (`step13DenseElsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open FullM6Sweep.M6ElsBv
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM6Sweep.M6SweepTactics

/-! ## 1. `S13ElsLitLoop`, Slice Steps & Watch-List Compaction -/

private structure S13ElsLitLoop (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) : Prop where
  dinv : FullDenseInvW c F0 F_cur sL
  cv : sL.core.cur_vars = s.core.cur_vars
  fuel : sL.core.fuel = s.core.fuel
  repr : FullCongReprInv F_cur (2 * sL.core.cur_vars) sL.core.repr
  tmk : sL.scratch.tarjan_mark = s.scratch.tarjan_mark
  trh : sL.scratch.tarjan_reach = s.scratch.tarjan_reach
  scr : sL.scratch.scratch_buf = s.scratch.scratch_buf
  ws1 : sL.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : sL.scratch.work_stk2 = s.scratch.work_stk2
  gu : sL.scratch.glue_used = s.scratch.glue_used

private theorem s13_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

private theorem s13_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

private theorem s13_elsLitLoop_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64} {Q : Post [.bool]}
    (h : S13ElsLitLoop c F0 F_cur s sL) (hmL : (FullMem c sL ⋆ R) mL)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (decide (sL.core.inconsistent = 0#64), ()) mL := by
  have hrp : FullCongReprInv F_cur (2 * s.core.cur_vars) sL.core.repr := by
    rw [← h.cv]; exact h.repr
  by_cases hinc : sL.core.inconsistent = 0#64
  · rw [decide_eq_true hinc]
    exact hQ true sL mL h.dinv h.cv h.fuel hrp h.tmk h.trh h.scr h.ws1 h.ws2 h.gu
      (fun hn => Bool.noConfusion hn) hmL
  · rw [decide_eq_false hinc]
    exact hQ false sL mL h.dinv h.cv h.fuel hrp h.tmk h.trh h.scr h.ws1 h.ws2 h.gu
      (fun _ => ⟨h.dinv.2.1.ext_sound.2 (h.dinv.2.1.inconsistent_sound hinc), hinc⟩) hmL

private theorem s13_list_set2_eq {α : Type _} (xs : List α) {i0 i1 a0 a1 : Nat}
    (hi0 : a0 = i0) (hi1 : a1 = i1) {v0 v0' v1 v1' : α} (hv0 : v0 = v0') (hv1 : v1 = v1') :
    (xs.set a0 v0).set a1 v1 = (xs.set i0 v0').set i1 v1' := by
  subst hi0 hi1 hv0 hv1; rfl

private theorem s13_els_wvec_pop_eq {k : Nat} (sL : FullState) (l : BitVec 32) {offL szL : Nat}
    (hk_le : k ≤ szL) (hk_lt : k < 2 ^ 64) (hoff_lt : offL + k < 2 ^ 32) (hsz_lt : szL < 2 ^ 32)
    (h2l0_c0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat)
    (h2l1_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1)
    {h0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length}
    {h1 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat < sL.core.wvec.length}
    (hoffL_bv :
      (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h0)).toNat =
        offL)
    (hszL_bv :
      (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) +
        (1 : BitVec 64)).toNat]'h1)).toNat = szL) :
    (sL.core.wvec.set (BitVec.setWidth 64 l <<< (1 : Nat)).toNat (BitVec.setWidth 32
        (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h0) +
          BitVec.ofNat 64 k))).set
      (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat
      (BitVec.setWidth 32 (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) +
        (1 : BitVec 64)).toNat]'h1) - BitVec.ofNat 64 k)) =
    (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + k))).set
      (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - k)) := by
  have hoff64 : offL < 2 ^ 64 := by omega
  have hsz64 : szL < 2 ^ 64 := by omega
  refine s13_list_set2_eq sL.core.wvec h2l0_c0 h2l1_c0 ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    have hv : BitVec.setWidth 64 (sL.core.wvec[_]'h0) = BitVec.ofNat 64 offL :=
      BitVec.eq_of_toNat_eq (by rw [hoffL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64])
    rw [hv, BitVec.toNat_setWidth, show (BitVec.ofNat 64 offL + BitVec.ofNat 64 k).toNat =
      offL + k by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt (by omega)],
      BitVec.toNat_ofNat]
  · apply BitVec.eq_of_toNat_eq
    have hv : BitVec.setWidth 64 (sL.core.wvec[_]'h1) = BitVec.ofNat 64 szL :=
      BitVec.eq_of_toNat_eq (by rw [hszL_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64])
    rw [hv, BitVec.toNat_setWidth, show (BitVec.ofNat 64 szL - BitVec.ofNat 64 k).toNat =
      szL - k by rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsz64, Nat.mod_eq_of_lt hk_lt]; omega,
      BitVec.toNat_ofNat]

private def s13ElsCompactExpr (c : FullCfg) (l ot : Val i32)
    (ooff_v oend_v : Val i64) (Jc2 : Cont []) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i64, i64, .bool]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p.fst, Arg.var oend_v, ()))
      fun p1 => Expr.jnz (Arg.var p1.fst)
      (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p2 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var p2.fst, ())) fun p3 =>
        Expr.load i32 (Arg.var p3.fst) fun ld =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p4 =>
        Expr.group (sig := [[i64, i64, .bool]]) (fun _ => Blocks.cons (fun q =>
          Expr.jump Js.fst (Arg.var q.fst, Arg.var q.snd.fst, Arg.var q.snd.snd.fst, ()))
          Blocks.nil) fun Js =>
        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 2147483648, ())) fun p5 =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var p5.fst, Arg.imm 0, ())) fun p6 =>
        Expr.jnz (Arg.var p6.fst)
          (Expr.group (sig := [[i64, .bool]]) (fun _ => Blocks.cons (fun q =>
            Expr.jump Js.fst (Arg.var p4.fst, Arg.var q.fst, Arg.var q.snd.fst, ()))
            Blocks.nil) fun Js =>
            Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun q8 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q8.fst, ()))
                fun q9 => Expr.store (t := i32) (Arg.var ld) (Arg.var q9.fst)
                (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.snd.fst, Arg.imm 1, ()))
                  fun q10 => Expr.jump Js.fst (Arg.var q10.fst, Arg.var p.snd.snd.fst, ())))
              Blocks.nil) fun Js1 =>
            Expr.jnz (Arg.var p.snd.snd.fst) (Expr.jump Js1.fst ())
              (Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 2147483647, ()))
                fun q7 => Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32)
                  (Arg.var q7.fst, Arg.var l, ())) fun q8 =>
                Expr.jnz (Arg.var q8.fst)
                  (Expr.jump Js.fst (Arg.var p.snd.fst, Arg.imm true, ()))
                  (Expr.jump Js1.fst ())))
          (Expr.group (sig := [[i64, i64]]) (fun _ => Blocks.cons (fun q7 =>
            Expr.jump Js.fst (Arg.var q7.fst, Arg.var q7.snd.fst, Arg.var p.snd.snd.fst, ()))
            Blocks.nil) fun Js =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p4.fst, Arg.var oend_v, ()))
              fun q7 => Expr.jnz (Arg.var q7.fst)
              (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun q8 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q8.fst, ()))
                  fun q9 => Expr.store (t := i32) (Arg.var ld) (Arg.var q9.fst)
                  (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.snd.fst, Arg.imm 1, ()))
                    fun q10 => Expr.let_ (Op.mk (OpCode.mul i64)
                      (Arg.var q10.fst, Arg.imm 4, ())) fun q11 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q11.fst, ()))
                      fun q12 => Expr.let_ (Op.mk (OpCode.mul i64)
                        (Arg.var p4.fst, Arg.imm 4, ())) fun q13 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var q13.fst, ()))
                        fun q14 => Expr.load i32 (Arg.var q14.fst) fun ld2 =>
                        Expr.store (t := i32) (Arg.var ld2) (Arg.var q12.fst)
                          (Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var p.snd.fst, Arg.imm 2, ())) fun r1 =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p4.fst, Arg.imm 1, ()))
                              fun r2 => Expr.jump Js.fst (Arg.var r2.fst, Arg.var r1.fst, ()))))
              (Expr.jump Js.fst (Arg.var p4.fst, Arg.var p.snd.fst, ()))))
      (Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun pk =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var pk.fst, Arg.var oend_v, ()))
          fun pk1 => Expr.jnz (Arg.var pk1.fst)
          (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pk.fst, Arg.imm 4, ())) fun pk2 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWstk, Arg.var pk2.fst, ()))
              fun pk3 => Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var pk3.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk.fst, Arg.imm 1, ())) fun pk4 =>
                Expr.jump Js.fst (Arg.var pk4.fst, ())))
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ot, ())) fun w4 =>
            Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun w5 =>
            Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var w4.fst, Arg.var w5.fst, ())) fun w6 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var w6.fst, Arg.imm 1, ())) fun w7 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var w7.fst, Arg.imm 4, ())) fun w8 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWvec, Arg.var w8.fst, ())) fun w9 =>
            Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var p.snd.fst, Arg.var ooff_v, ()))
              fun w10 => Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var w10.fst, ()))
              fun w11 => Expr.store (t := i32) (Arg.var w11.fst) (Arg.var w9.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun u1 =>
                Expr.load i64 (Arg.var u1.fst) fun ldu =>
                Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var oend_v, Arg.var p.snd.fst, ()))
                  fun u2 => Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var ldu, Arg.var u2.fst, ())) fun u3 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun u4 =>
                  Expr.store (t := i64) (Arg.var u3.fst) (Arg.var u4.fst)
                    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                      Expr.jump Jc2 ()) Blocks.nil) fun Js =>
                      Expr.jnz (Arg.var p.snd.snd.fst)
                        (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 504, ()))
                          fun n1 => Expr.load i64 (Arg.var n1.fst) fun ldn =>
                          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64)
                            (Arg.var ldn, Arg.imm 0, ())) fun n2 =>
                          Expr.jnz (Arg.var n2.fst)
                            (Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.hdr, Arg.imm 504, ())) fun n3 =>
                              Expr.load i64 (Arg.var n3.fst) fun ldn2 =>
                              Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var ldn2, Arg.imm 1, ()))
                                fun n4 => Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.hdr, Arg.imm 504, ())) fun n5 =>
                                Expr.store (t := i64) (Arg.var n4.fst) (Arg.var n5.fst)
                                  (Expr.jump Js.fst ()))
                            (Expr.jump Js.fst ()))
                        (Expr.jump Js.fst ()))))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var p.snd.fst, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var ooff_v, Arg.var ooff_v, Arg.imm false, ())

private theorem s13_els_compact_ot_watches {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {l ot : BitVec 32} {ooff_v oend_v : BitVec 64}
    {Jc2 : Cont []}
    (hinv1 : FullDenseInvW c F0 F_cur s1) (hot_lt : ot.toNat < 2 * s1.core.cur_vars)
    (hosz_pos : 0 < fullWatchSize s1 ot.toNat)
    (hooff_v : ooff_v = BitVec.ofNat 64 (fullWatchOff s1 ot.toNat))
    (hoend_v : oend_v = BitVec.ofNat 64 (fullWatchOff s1 ot.toNat + fullWatchSize s1 ot.toNat))
    (hm1 : (FullMem c s1 ⋆ R) m)
    (hCont : ∀ (wvec' wstk' : List (BitVec 32)) (wu' nb' : BitVec 64) (mf : Mem 64),
      FullDenseInvW c F0 F_cur { s1 with core := { s1.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } →
      (FullMem c { s1 with core := { s1.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } ⋆ R) mf →
      Jc2 () mf) :
    wp Γ Q X (s13ElsCompactExpr c l ot ooff_v oend_v Jc2) m := by
  unfold s13ElsCompactExpr
  have hcl1 := hinv1.1.core_ok; have hwm1 := hinv1.2.1.watches; unfold ModeWatchesInv at hwm1
  rw [ite_eq_right (fun h0 => hinv1.2.2.2.2.2.2 h0)] at hwm1
  have hwc := c.hwcap; unfold dimacsBound at hwc
  let ooff := fullWatchOff s1 ot.toNat; let osz := fullWatchSize s1 ot.toNat; let oend := ooff + osz
  have hbd_ot := hwm1.layout.bounds ot.toNat hot_lt
  have hwlen_le1 := hcl1.wlen_le; have hwstk_len1 := hcl1.wstk_len_arr
  have hoend_le : oend ≤ s1.core.wstk.length := by
    dsimp only [oend, ooff, osz]; rw [hwstk_len1]; exact Nat.le_trans hbd_ot hwlen_le1
  have hoend_cap : oend ≤ c.wcap := hwstk_len1 ▸ hoend_le
  have hoend_lt64 : oend < 2 ^ 64 := by omega
  have hosz_lt32 : osz < 2 ^ 32 := by
    unfold osz fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
  have hooff_bv : ooff_v.toNat = ooff := by
    rw [hooff_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hoend_bv : oend_v.toNat = oend := by
    rw [hoend_v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoend_lt64]
  have hslice_ot := hwm1.slices ot.toNat hot_lt
  refine wp_while_state (ts := [i64, i64, .bool])
    (proj := fun p : BitVec 64 × BitVec 64 × Bool => (p.1, p.2.1, p.2.2, ()))
    (μ := fun p => oend - p.1.toNat)
    (Inv := fun (op, oq, _orem) mop => ooff ≤ oq.toNat ∧ oq.toNat ≤ op.toNat ∧
      op.toNat ≤ oend ∧ ∃ wstkL : List (BitVec 32), wstkL.length = c.wcap ∧
        (∀ i, i < ooff ∨ op.toNat ≤ i → wstkL[i]? = s1.core.wstk[i]?) ∧
        DenseWatchSliceOk F_cur { s1.core with wstk := wstkL } ot.toNat ooff (oq.toNat - ooff) ∧
        DenseWatchSliceOk F_cur s1.core ot.toNat op.toNat (oend - op.toNat) ∧
        (FullMem c { s1 with core := { s1.core with wstk := wstkL } } ⋆ R) mop) ?_ ?_
  · intro J1 hJ1; c0_hsteps!
    refine hJ1 (ooff_v, ooff_v, false) _ ⟨by rw [hooff_bv]; exact le_refl _,
      by rw [hooff_bv]; exact le_refl _, by rw [hooff_bv]; omega,
      s1.core.wstk, hwstk_len1, fun _ _ => rfl, ?_, ?_, hm1⟩
    · rw [hooff_bv, Nat.sub_self]; exact .empty
    · rw [hooff_bv]; change DenseWatchSliceOk F_cur s1.core ot.toNat ooff ((ooff + osz) - ooff)
      rw [Nat.add_sub_cancel_left]; exact hslice_ot
  · rintro J1 ⟨op, oq, orem⟩ mop
      ⟨hooff_oq, hoq_op, hop_end, wstkL, hwlL, houtL, hsl_pre, hsl_suf, hmop⟩ ih1
    c0_hsplit
    · have hop_lt : op.toNat < oend := by rw [← hoend_bv]; exact hc
      have hop_bd : op.toNat < wstkL.length := by rw [hwlL]; omega
      have hop1 : (op + 1#64).toNat = op.toNat + 1 := by bv_omega
      let ow := wstkL[op.toNat]'hop_bd
      have how_s : s1.core.wstk[op.toNat]? = some ow := by
        have hq := houtL op.toNat (Or.inr (le_refl _)); rw [← hq, List.getElem?_eq_getElem hop_bd]
      c0_hsteps_nogrp
      refine wp_unroll_group fun Jbin hJbin => ?_
      c0_hsplit
      · have how_bin : (ow &&& 0x80000000#32) ≠ 0#32 := by
          rw [show (0x80000000#32 : BitVec 32) = (2147483648 : BitVec 32) from rfl]
          dsimp only [ow]; exact hc
        obtain ⟨how_ne, how_lt, hent_ow, hsl_suf1⟩ :=
          s13_denseSlice_step_bin hsl_suf (by omega) how_s how_bin
        have hoq_bd : oq.toNat < wstkL.length := by rw [hwlL]; omega
        have hoq1 : (oq + 1#64).toNat = oq.toNat + 1 := by bv_omega
        let wstkL' := wstkL.set oq.toNat ow
        have hsl_pre' : DenseWatchSliceOk F_cur { s1.core with wstk := wstkL' }
            ot.toNat ooff (oq.toNat + 1 - ooff) := by
          rw [show oq.toNat + 1 - ooff = (oq.toNat - ooff) + 1 by omega]
          refine DenseWatchSliceOk.append_bin (k := { s1.core with wstk := wstkL })
            (k' := { s1.core with wstk := wstkL' }) (le_refl _) (fun _ r => r)
            (fun idx hidx => by simp only [wstkL']; rw [List.getElem?_set_ne (by omega)])
            hsl_pre ?_ how_bin how_ne how_lt hent_ow
          simp only [wstkL']
          rw [show ooff + (oq.toNat - ooff) = oq.toNat by omega, List.getElem?_set_self hoq_bd]
        have hkeep : ∀ (orem' : Bool) (m' : Mem 64),
            (FullMem c { s1 with core := { s1.core with wstk := wstkL' } } ⋆ R) m' →
            J1 (op + 1#64, oq + 1#64, orem', ()) m' := fun orem' m' hm' =>
          ih1 (op + 1#64, oq + 1#64, orem') m' (by dsimp only; rw [hop1]; omega)
            ⟨by rw [hoq1]; omega, by rw [hoq1, hop1]; omega, by rw [hop1]; omega, wstkL',
             by rw [List.length_set, hwlL], fun i hi => by
               simp only [wstkL']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
               exact houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi),
             by rw [hoq1]; exact hsl_pre', by
               rw [hop1, show oend - (op.toNat + 1) = oend - op.toNat - 1 by omega]; exact hsl_suf1,
             hm'⟩
        refine wp_unroll_group fun Jrem hJrem => ?_
        c0_hsteps!
        all_goals first
          | exact hkeep _ _ (by assumption)
          | exact ih1 (op + 1#64, oq, true) _ (by dsimp only; rw [hop1]; omega)
              ⟨hooff_oq, by rw [hop1]; omega, by rw [hop1]; omega, wstkL, hwlL,
               (fun i hi => houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi)),
               hsl_pre, by rw [hop1, show oend - (op.toNat + 1) = oend - op.toNat - 1 by omega]
                           exact hsl_suf1,
               by assumption⟩
      · have how_occ : (ow &&& 0x80000000#32) = 0#32 := by
          rw [show (0x80000000#32 : BitVec 32) = (2147483648 : BitVec 32) from rfl]
          dsimp only [ow]; exact hc
        obtain ⟨hrem2, hsz3, cr_w, hcr_s, hcr_lt, hcr_ref, hsl_suf2⟩ :=
          s13_denseSlice_step_occ hsl_suf (by omega) how_s how_occ
        have hop1_lt : (op + 1#64).toNat < oend := by rw [hop1]; omega
        have hop2 : (op + 1#64 + 1#64).toNat = op.toNat + 2 := by bv_omega
        have hop1_bd : (op + 1#64).toNat < wstkL.length := by rw [hwlL]; omega
        have hoq_bd : oq.toNat < wstkL.length := by rw [hwlL]; omega
        have hoq1 : (oq + 1#64).toNat = oq.toNat + 1 := by bv_omega
        have hoq2 : (oq + 2#64).toNat = oq.toNat + 2 := by bv_omega
        have hcr_L : wstkL[(op + 1#64).toNat]'hop1_bd = cr_w := by
          have h1 := houtL (op.toNat + 1) (Or.inr (by omega))
          rw [← hop1, List.getElem?_eq_getElem hop1_bd] at h1
          rw [← hop1] at hcr_s; exact Option.some.inj (h1.trans hcr_s)
        have hmem_occ : (wstkL.set oq.toNat ow)[(op + 1#64).toNat]'(by
            rw [List.length_set]; exact hop1_bd) = cr_w := by
          rw [List.getElem_set_ne (by rw [hop1]; omega)]; exact hcr_L
        let wstkL' := (wstkL.set oq.toNat ow).set (oq.toNat + 1) cr_w
        have hsl_pre' : DenseWatchSliceOk F_cur { s1.core with wstk := wstkL' }
            ot.toNat ooff (oq.toNat + 2 - ooff) := by
          rw [show oq.toNat + 2 - ooff = (oq.toNat - ooff) + 2 by omega]
          refine DenseWatchSliceOk.append_occ (k := { s1.core with wstk := wstkL })
            (k' := { s1.core with wstk := wstkL' }) (le_refl _) (fun _ r => r) (fun idx hidx => by
              simp only [wstkL']
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            hsl_pre ?_ ?_ how_occ hsz3 hcr_lt hcr_ref
          · simp only [wstkL']; rw [show ooff + (oq.toNat - ooff) = oq.toNat by omega,
              List.getElem?_set_ne (by omega), List.getElem?_set_self hoq_bd]
          · simp only [wstkL']; rw [show ooff + (oq.toNat - ooff) + 1 = oq.toNat + 1 by omega,
              List.getElem?_set_self (by rw [List.length_set, hwlL]; omega)]
        have hwstk_eq : (wstkL.set oq.toNat (wstkL[op.toNat]'hop_bd)).set
            (oq + (1 : BitVec 64)).toNat ((wstkL.set oq.toNat
              (wstkL[op.toNat]'hop_bd))[(op + (1 : BitVec 64)).toNat]'(by
              rw [List.length_set]; exact hop1_bd)) = wstkL' := by
          have hoq1' : (oq + (1 : BitVec 64)).toNat = oq.toNat + 1 := hoq1
          have hmem' : (wstkL.set oq.toNat (wstkL[op.toNat]'hop_bd))[(op +
              (1 : BitVec 64)).toNat]'(by rw [List.length_set]; exact hop1_bd) = cr_w := hmem_occ
          simp only [wstkL', ow]; rw [hoq1', hmem']
        c0_hsteps!
        exact ih1 (op + 1#64 + 1#64, oq + 2#64, orem) _ (by dsimp only; rw [hop2]; omega)
          ⟨by rw [hoq2]; omega, by rw [hoq2, hop2]; omega, by rw [hop2]; omega,
           wstkL', by rw [List.length_set, List.length_set, hwlL], fun i hi => by
             simp only [wstkL']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
               List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
             exact houtL i (Or.imp (fun _ => by omega) (fun _ => by omega) hi),
           by rw [hoq2]; exact hsl_pre', by
             rw [hop2, show oend - (op.toNat + 2) = oend - op.toNat - 2 by omega]; exact hsl_suf2,
           by dsimp only at hm ⊢; rwa [← hwstk_eq]⟩
    · have hop_eq : op.toNat = oend := by
        have hge : oend_v.toNat ≤ op.toNat := Nat.le_of_not_lt hc; rw [hoend_bv] at hge; omega
      rw [hop_eq] at houtL; clear hsl_suf hslice_ot hwm1 hbd_ot; c0_hsteps_nogrp
      refine wp_while_state (ts := [i64]) (proj := fun ok : BitVec 64 => (ok, ()))
        (μ := fun ok => oend - ok.toNat)
        (Inv := fun ok mok => oq.toNat ≤ ok.toNat ∧ ok.toNat ≤ oend ∧
          ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
            (∀ i, i < ooff ∨ oend ≤ i → wstkK[i]? = s1.core.wstk[i]?) ∧
            (∀ i, ooff ≤ i → i < oq.toNat → wstkK[i]? = wstkL[i]?) ∧
            (FullMem c { s1 with core := { s1.core with wstk := wstkK } } ⋆ R) mok) ?_ ?_
      · intro J2 hJ2; c0_hsteps!
        exact hJ2 oq _ ⟨le_refl _, by omega, wstkL, hwlL, houtL, fun _ _ _ => rfl, hmop⟩
      · rintro J2 ok mok ⟨hok_lo, hok_hi, wstkK, hwlK, houtK, hpreK, hmok⟩ ih2
        c0_hsplit
        · have hok_lt : ok.toNat < oend := by rw [← hoend_bv]; exact hc
          have hok_bd : ok.toNat < wstkK.length := by rw [hwlK]; omega
          have hok1 : (ok + 1#64).toNat = ok.toNat + 1 := by bv_omega
          let wstkK' := wstkK.set ok.toNat 0xFFFFFFFF#32; c0_hsteps!
          exact ih2 (ok + 1#64) _ (by rw [hok1]; omega)
            ⟨by rw [hok1]; omega, by rw [hok1]; omega, wstkK', by rw [List.length_set, hwlK],
             fun i hi => by
               simp only [wstkK']; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega)]
               exact houtK i hi,
             fun i hi1 hi2 => by
               simp only [wstkK']; rw [List.getElem?_set_ne (by omega)]; exact hpreK i hi1 hi2,
             by assumption⟩
        · let newSz := oq.toNat - ooff
          have hle_oq : oq.toNat ≤ oend := Nat.le_trans hok_lo hok_hi
          have hle_sz : newSz ≤ osz := by omega
          have hnew_c0 : (oq - ooff_v).setWidth 32 = BitVec.ofNat 32 newSz := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_sub, hooff_bv, BitVec.toNat_ofNat]
            have hlt32 : newSz < 2 ^ 32 := Nat.lt_of_le_of_lt hle_sz hosz_lt32
            have hlt64 : newSz < 2 ^ 64 := Nat.lt_trans hlt32 (by decide)
            rw [show (2 ^ 64 - ooff + oq.toNat) % 2 ^ 64 = newSz by omega,
              Nat.mod_eq_of_lt hlt32]
          have hwu_c0 : oend_v - oq = BitVec.ofNat 64 (oend - oq.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sub, hoend_bv, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : oend - oq.toNat < 2 ^ 64)]; omega
          have h2ot1_c0 : (ot.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * ot.toNat + 1 := by
            rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
              show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h2ot1_bd : (ot.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s1.core.wvec.length := by
            have := hcl1.cur_vars_le; rw [h2ot1_c0, hcl1.wvec_len]; omega
          have hslK : DenseWatchSliceOk F_cur { s1.core with wstk := wstkK } ot.toNat ooff
              newSz := DenseWatchSliceOk.relocate (k := { s1.core with wstk := wstkL })
              (k' := { s1.core with wstk := wstkK })
              (by rw [CNF.entails_def]; exact fun _ h => h) (le_refl _) (fun _ r => r)
              (fun idx hidx => hpreK (ooff + idx) (by omega) (by omega)) hsl_pre
          have hinv_k : ∀ (wu' nb' : BitVec 64), FullDenseInvW c F0 F_cur
                { s1 with core := { s1.core with
                    wvec := s1.core.wvec.set (2 * ot.toNat + 1) (BitVec.ofNat 32 newSz),
                    wstk := wstkK, wusable := wu', num_binary := nb' } } := fun wu' nb' =>
            m6_denseInvW_watchCompact hinv1 hot_lt hle_sz hwlK houtK hslK wu' nb'
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () mf => ∃ nb' : BitVec 64,
              (FullMem c { s1 with core := { s1.core with
                  wvec := s1.core.wvec.set (2 * ot.toNat + 1) (BitVec.ofNat 32 newSz),
                  wstk := wstkK, wusable := s1.core.wusable + BitVec.ofNat 64 (oend - oq.toNat),
                  num_binary := nb' } } ⋆ R) mf) ?_ ?_
          · rintro _ ⟨⟩ mf ⟨nb', hmf⟩; c0_hsteps!
            exact hCont _ _ _ _ mf (hinv_k _ nb') hmf
          · intro Jnb hJnb; c0_hsplit
            · c0_hsplit
              · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary - 1#64, ?_⟩
                rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption
              · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary, ?_⟩
                rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption
            · c0_hsteps!; refine hJnb () _ ⟨s1.core.num_binary, ?_⟩
              rw [← h2ot1_c0, ← hnew_c0, ← hwu_c0]; assumption

/-! ## 2. `full_m6_els_lit_s13_wp` (`step13ElsLitSpec`) -/

private theorem s13_els_lit_post_compact_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sC : FullState}
    {rl ot : BitVec 32} {gL : BitVec 64} {R : Mem 64 → Prop} {mC : Mem 64}
    {L : Cont [i64]}
    (hL : ∀ xs : BitVec 64 × FullState, ∀ m', xs.1.toNat < gL.toNat →
      (S13ElsLitLoop c F0 F_cur s xs.2 ∧ (FullMem c xs.2 ⋆ R) m') → L (xs.1, ()) m')
    (hLoopC : S13ElsLitLoop c F0 F_cur s sC)
    (hg_pos : 0 < gL.toNat) (hg1 : (gL - 1#64).toNat = gL.toNat - 1)
    (hrl_lt : rl.toNat < 2 * s.core.cur_vars)
    (hot_lt : ot.toNat < 2 * sC.core.cur_vars)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, ot.toNat]))
    (hmC : (FullMem c sC ⋆ R) mC)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let e_post := Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) fun (r64, ()) =>
      Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl)
        (Arg.var r64, Arg.var (BitVec.ofNat 64 s.core.cur_vars <<< 1#64), ())) fun (bge, ()) =>
      Expr.jnz (Arg.var bge) (Expr.jump L (Arg.var (gL - 1#64), ()))
        (Expr.let_ (Op.mk (.xor i32) (Arg.var ot, Arg.imm 1, ())) fun (rot1, ()) =>
        Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var rl, Arg.var rot1, ())) fun (beq1, ()) =>
        Expr.jnz (Arg.var beq1) (Expr.jump L (Arg.var (gL - 1#64), ()))
          (Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var rl, Arg.var ot, ())) fun (beq0, ()) =>
          Expr.jnz (Arg.var beq0)
            (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
              (Arg.var c.hdr, Arg.var rl, ()) fun (okU, ()) =>
            Expr.jnz (Arg.var okU) (Expr.jump L (Arg.var (gL - 1#64), ()))
              (Expr.ret (Arg.imm false, ())))
            (Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
              (Arg.var c.hdr, Arg.var rl, Arg.var ot, ()) fun (rB, ()) =>
            Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var rB, Arg.imm 20, ()))
              fun (b20, ()) =>
            Expr.jnz (Arg.var b20) (Expr.ret (Arg.imm false, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var rB, Arg.imm 2, ()))
                fun (b2, ()) =>
              Expr.jnz (Arg.var b2)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun (po, ()) =>
                Expr.store (t := i64) (Arg.imm 1) (Arg.var po) (Expr.ret (Arg.imm true, ())))
                (Expr.jump L (Arg.var (gL - 1#64), ()))))))
    wp Γ Q X e_post mC := by
  intro e_post
  have hinvC := hLoopC.dinv; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinvC.1.core_ok.cur_vars_le
  have hrpC : FullCongReprInv F_cur (2 * s.core.cur_vars) sC.core.repr := by
    rw [← hLoopC.cv]; exact hLoopC.repr
  c0_hsplit
  · exfalso
    have hge : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat ≤ ot.toNat := by
      simpa only [bv_c0, BitVec.toNat_ofNat] using ‹_›
    rw [← hLoopC.cv, m6_els_bv64_shl1_nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hge
    omega
  c0_hsplit
  · c0_hsteps!; exact hL (gL - 1#64, sC) mC (by dsimp only; omega) ⟨hLoopC, hmC⟩
  c0_hsplit
  · have hrr : rl = ot := ‹_›
    rw [← hrr] at hent_bin
    have hent_u := m6_entails_unit_of_dup hent_bin
    c0_hsteps_nogrp; c0_call hAddUnit
    refine ⟨c, F0, F_cur, sC, R, rfl, hinvC.1, hinvC.2.1, fun _ => hent_u, hmC, ?_⟩
    intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU hlenU hwU hclU hfail _ hmU
    have hinvU := m6_denseInvW_after_addUnit hinvC hlenU hwU hclU
    have hrpU : FullCongReprInv F_cur (2 * sU.core.cur_vars) sU.core.repr := by
      dsimp only [sU]; rw [show sC.core.cur_vars = sC.core.cur_vars from rfl]; exact hLoopC.repr
    c0_hsplit
    · c0_hsteps!
      exact hL (gL - 1#64, sU) mU (by dsimp only; omega)
        ⟨⟨hinvU, hLoopC.cv, hLoopC.fuel, hrpU, hLoopC.tmk, hLoopC.trh, hLoopC.scr,
          hLoopC.ws1, hLoopC.ws2, hLoopC.gu⟩, hmU⟩
    · have hokf : okU = false := by
        cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
      c0_hsteps!
      exact hQ false sU mU hinvU hLoopC.cv hLoopC.fuel hrpC hLoopC.tmk hLoopC.trh hLoopC.scr
        hLoopC.ws1 hLoopC.ws2 hLoopC.gu (fun _ => hfail (by rw [hLoopC.cv]; exact hrl_lt) hokf) hmU
  · c0_hsteps_nogrp; c0_call hAddBin
    refine ⟨c, F0, F_cur, sC, R, rfl, hinvC.1, hinvC.2.1, hinvC.2.2.2.2.2.1,
      fun _ _ => hent_bin, hmC, ?_⟩
    intro rB vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
      nb' oom' inc' phases' wsort' mB sB hlenB hwB _ hr20 _ hmB
    have hinvB := s13_denseInvW_after_addBin hinvC hlenB hwB
    have hrpB : FullCongReprInv F_cur (2 * sB.core.cur_vars) sB.core.repr := by
      dsimp only [sB]; exact hLoopC.repr
    c0_hsplit
    · have hrB : rB = 20#64 := by bv_omega
      c0_hsteps!
      exact hQ false sB mB hinvB hLoopC.cv hLoopC.fuel hrpC hLoopC.tmk hLoopC.trh hLoopC.scr
        hLoopC.ws1 hLoopC.ws2 hLoopC.gu (fun _ => hr20 hrB) hmB
    c0_hsplit
    · c0_hsteps!
      exact hQ true { sB with core := { sB.core with oom := 1#64 } } _
        (s13_denseInvW_set_oom hinvB) hLoopC.cv hLoopC.fuel hrpC hLoopC.tmk hLoopC.trh
        hLoopC.scr hLoopC.ws1 hLoopC.ws2 hLoopC.gu (fun h => Bool.noConfusion h) (by assumption)
    · c0_hsteps!
      exact hL (gL - 1#64, sB) mB (by dsimp only; omega)
        ⟨⟨hinvB, hLoopC.cv, hLoopC.fuel, hrpB, hLoopC.tmk, hLoopC.trh, hLoopC.scr,
          hLoopC.ws1, hLoopC.ws2, hLoopC.gu⟩, hmB⟩

/-- Step-13 `full_m6_els_lit` (`FullCongReprInv`, `u32 rot = ot` without repr lookup). -/
theorem full_m6_els_lit_s13_wp (Γ : Env)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hElsAr : ∀ a m Q X, step13ElsArSpec a m Q X →
      Γ "full_m6_els_ar" [i64, i32, i32] [.bool] a m Q X) :
    ∀ args m Q X, step13ElsLitSpec args m Q X →
      Func.wp Γ full_m6_els_lit_body args m Q X := by
  rintro ⟨h, l, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hl_lt, hrl_lt, hlr_eq, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hmx := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le
  have h2l_bd : 2 * l.toNat + 1 < s.core.wvec.length := by rw [hcl.wvec_len]; omega
  unfold Func.wp full_m6_els_lit_body
  c0_hsteps_nogrp
  refine wp_while_break_state (brkTs := [i64]) (lpTs := [i64]) (β := BitVec 64 × FullState)
    (fun p => (p.1, ())) (fun p mB => S13ElsLitLoop c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) mB)
    (α := BitVec 64 × FullState) (fun p => (p.1, ())) (fun p => p.1.toNat)
    (fun p ml => S13ElsLitLoop c F0 F_cur s p.2 ∧ (FullMem c p.2 ⋆ R) ml) ?_ ?_ ?_
  · rintro B ⟨_gB, sB⟩ mB ⟨hB, hmB⟩; c0_hsteps!
    exact s13_elsLitLoop_exit hB hmB hQ
  · rintro B L ⟨gL, sL⟩ ml hB hL ⟨hLoop, hmL⟩
    dsimp only at *
    have hinvL := hLoop.dinv; have hclL := hinvL.1.core_ok; have hwL := hinvL.2.1
    have hcvL_le := hclL.cur_vars_le; have hl_ltL : l.toNat < 2 * sL.core.cur_vars := by
      rw [hLoop.cv]; exact hl_lt
    have h2l_bdL : 2 * l.toNat + 1 < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have h2l_mod : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 :=
      Nat.mod_eq_of_lt (by omega)
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    c0_hsplit; rotate_left; · c0_hsteps!; exact hB (gL, sL) ml ⟨hLoop, hmL⟩
    have hg_pos : 0 < gL.toNat := by bv_omega
    have hsz_pos : 0 < fullWatchSize sL l.toNat := by
      unfold fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
      have hpc : 0 < (sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
          rw [h2l_mod]; exact h2l_bdL)).toNat := by assumption
      rwa [← congrArg BitVec.toNat (m6_getElem_congr h2l_mod (by
        rw [h2l_mod]; exact h2l_bdL) h2l_bdL)]
    have hwmL := hwL.watches; unfold ModeWatchesInv at hwmL
    rw [ite_eq_right (fun h0 => hinvL.2.2.2.2.2.2 h0)] at hwmL
    have hbd_l := hwmL.layout.bounds l.toNat hl_ltL
    have hslice_l := hwmL.slices l.toNat hl_ltL
    let offL := fullWatchOff sL l.toNat; let szL := fullWatchSize sL l.toNat
    have hoff_def : offL = fullWatchOffCore sL.core l.toNat := rfl
    have hsz_def : szL = fullWatchSizeCore sL.core l.toNat := rfl
    have hoffL_lt : offL < sL.core.wstk.length := by
      have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
    have h2l0_c0 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat := by
      rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
    have h2l1_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat =
        2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
        show ((1 : BitVec 64)).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoffL_bv : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
          rw [h2l0_c0, hclL.wvec_len]; omega))).toNat = offL := by
      rw [bv_c0_zext32_64, m6_getElem_congr h2l0_c0
        (by rw [h2l0_c0, hclL.wvec_len]; omega) (by rw [hclL.wvec_len]; omega)]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hclL.wvec_len]; omega), Option.getD_some]
    have hszL_bv : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
          rw [h2l1_c0, hclL.wvec_len]; omega))).toNat = szL := by
      rw [bv_c0_zext32_64, m6_getElem_congr h2l1_c0
        (by rw [h2l1_c0, hclL.wvec_len]; omega) h2l_bdL]
      unfold szL fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
    have hws_off_lt : (BitVec.setWidth 64
        (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'(by
          rw [h2l0_c0, hclL.wvec_len]; omega))).toNat < sL.core.wstk.length := by
      rw [hoffL_bv]; exact hoffL_lt
    have hw0_c0_eq : ∀ (h1 : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat < sL.core.wvec.length)
        (h2 : (BitVec.setWidth 64
            (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h1)).toNat <
          sL.core.wstk.length),
        sL.core.wstk[(BitVec.setWidth 64
          (sL.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'h1)).toNat]'h2 =
        sL.core.wstk[offL]'hoffL_lt := fun h1 h2 => m6_getElem_congr hoffL_bv h2 hoffL_lt
    have hg1 : (gL - 1#64).toNat = gL.toNat - 1 := by bv_omega
    have h2l0_mod : (2 * l.toNat) % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
    have h2l0_bdL : 2 * l.toNat < sL.core.wvec.length := by rw [hclL.wvec_len]; omega
    have hwv0_eq : (sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
        rw [h2l0_mod]; exact h2l0_bdL)).toNat = offL := by
      rw [m6_getElem_congr h2l0_mod (by rw [h2l0_mod]; exact h2l0_bdL) h2l0_bdL]
      unfold offL fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem h2l0_bdL, Option.getD_some]
    have hwstk_len_L := hclL.wstk_len_arr; have hwlen_le_L := hclL.wlen_le
    c0_hsplit
    · have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_bin : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) ≠ 0#32 := by
        have hnc : ¬ (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32 := by
          first
          | exact ‹¬ (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32›
          | (have hh := ‹¬ sL.core.wstk[(BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< 1).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega))).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hw0_c0_eq] at hh)
          | (have hh := ‹¬ sL.core.wstk[(sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
                rw [h2l0_mod]; exact h2l0_bdL)).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hwv0_eq] at hh)
        simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hnc
      obtain ⟨_, hot_lt, hent_bin, hsl_nxt⟩ := s13_denseSlice_step_bin hslice_l hsz_pos hw0_some
        hw0_bin
      let ot := sL.core.wstk[offL]'hoffL_lt &&& 0x7FFFFFFF#32
      let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 1))).set
        (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 1))
      obtain ⟨s1, hs1_def⟩ : ∃ s1 : FullState, s1 = { sL with core := { sL.core with
          wvec := wvec1, wusable := sL.core.wusable + 1#64 } } := ⟨_, rfl⟩
      have hinv1 : FullDenseInvW c F0 F_cur s1 :=
        hs1_def.symm ▸ m6_denseInvW_watchPop hinvL hl_ltL (by omega : 1 ≤ szL)
          (sL.core.wusable + 1#64) hsl_nxt
      have hent_rl_ot : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, ot.toNat]) :=
        m6_entails_bin_subst hlr_eq (LitEquiv.refl _ _) hent_bin
      have hsz_lt32 : szL < 2 ^ 32 := by
        unfold szL fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
      have hwv_pop1 := s13_els_wvec_pop_eq (k := 1) sL l (by omega) (by decide) (by omega) hsz_lt32
        h2l0_c0 h2l1_c0 hoffL_bv hszL_bv
      c0_hsteps_nogrp
      let ot_c0 := sL.core.wstk[(BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
        (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega))).toNat]'hws_off_lt &&&
        (2147483647 : BitVec 32)
      have hot_c0_eq : ot_c0 = ot := by dsimp only [ot_c0, ot]; rw [hw0_c0_eq]; rfl
      have hpop1_m : (FullMem c s1 ⋆ R) m := by
        rw [hs1_def]; dsimp only [wvec1]; rw [← hwv_pop1]; assumption
      refine wp_join_group (ts := []) (fun () mC =>
          ∃ sC : FullState, S13ElsLitLoop c F0 F_cur s sC ∧ (FullMem c sC ⋆ R) mC) ?_ ?_
      · rintro _ ⟨⟩ mC ⟨sC, hLoopC, hmC⟩
        have hot_ltC : ot.toNat < 2 * sC.core.cur_vars := by
          rw [hLoopC.cv, ← hLoop.cv]; exact hot_lt
        have hot_c0_lt : ot_c0.toNat < 2 * sC.core.cur_vars := by
          rw [hot_c0_eq]; exact hot_ltC
        have hent_c0 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [rl.toNat, ot_c0.toNat]) := by
          rw [hot_c0_eq]; exact hent_rl_ot
        exact s13_els_lit_post_compact_wp (ot := ot_c0) hAddUnit hAddBin
          (fun xs m' hlt => hL xs m' hlt) hLoopC hg_pos hg1 hrl_lt hot_c0_lt hent_c0 hmC hQ
      · intro Jc hJc
        have hcl1 := hinv1.1.core_ok
        have hcv1_eq : s1.core.cur_vars = s.core.cur_vars := hs1_def.symm ▸ hLoop.cv
        have hw1 := hinv1.2.1; have hwm1 := hw1.watches; unfold ModeWatchesInv at hwm1
        rw [ite_eq_right (fun h0 => hinv1.2.2.2.2.2.2 h0)] at hwm1
        have hot_lt1 : ot.toNat < 2 * s1.core.cur_vars := by rw [hcv1_eq, ← hLoop.cv]; exact hot_lt
        have h2ot0_lt : 2 * ot.toNat < 4 * c.max_vars := by omega
        have h2ot1_lt : 2 * ot.toNat + 1 < 4 * c.max_vars := by omega
        have h2ot0_wvec : 2 * ot.toNat < s1.core.wvec.length := hcl1.wvec_len ▸ h2ot0_lt
        have h2ot1_wvec : 2 * ot.toNat + 1 < s1.core.wvec.length := hcl1.wvec_len ▸ h2ot1_lt
        have h2ot0_bd : (ot.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length := by
          rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, hcl1.wvec_len, Nat.mod_eq_of_lt (by omega)]
          exact h2ot0_lt
        have h2ot1_bd : (ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            s1.core.wvec.length := by
          rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
            show ((1 : BitVec 64)).toNat = 1 from rfl, hcl1.wvec_len,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h2ot1_lt
        c0_hsplit; rotate_left
        · c0_hsteps!
          exact hJc () _ ⟨s1, ⟨hinv1, hcv1_eq, hs1_def.symm ▸ hLoop.fuel,
            hs1_def.symm ▸ hLoop.repr, hs1_def.symm ▸ hLoop.tmk, hs1_def.symm ▸ hLoop.trh,
            hs1_def.symm ▸ hLoop.scr, hs1_def.symm ▸ hLoop.ws1, hs1_def.symm ▸ hLoop.ws2,
            hs1_def.symm ▸ hLoop.gu⟩, hpop1_m⟩
        let ooff := fullWatchOff s1 ot.toNat; let osz := fullWatchSize s1 ot.toNat
        let oend := ooff + osz
        have h2ot0_eq : (ot.setWidth 64 <<< (1 : Nat)).toNat = 2 * ot.toNat := by
          rw [m6_els_bv64_shl1_nat, bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
        have h2ot1_eq : (ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat =
            2 * ot.toNat + 1 := by
          rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
            show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hooff_bv : (BitVec.setWidth 64
            (s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd)).toNat = ooff := by
          rw [bv_c0_zext32_64, m6_getElem_congr h2ot0_eq h2ot0_bd h2ot0_wvec]
          unfold ooff fullWatchOff fullWatchOffCore
          rw [@List.getElem?_eq_getElem _ s1.core.wvec (2 * ot.toNat) h2ot0_wvec, Option.getD_some]
        have hosz_bv : (BitVec.setWidth 64
            (s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat]'
              h2ot1_bd)).toNat = osz := by
          rw [bv_c0_zext32_64, m6_getElem_congr h2ot1_eq h2ot1_bd h2ot1_wvec]
          unfold osz fullWatchSize fullWatchSizeCore
          rw [@List.getElem?_eq_getElem _ s1.core.wvec (2 * ot.toNat + 1) h2ot1_wvec,
            Option.getD_some]
        have hbd_ot := hwm1.layout.bounds ot.toNat hot_lt1
        have hwlen_le1 := hcl1.wlen_le; have hwstk_len1 := hcl1.wstk_len_arr
        have hoend_le : oend ≤ s1.core.wstk.length := by
          dsimp only [oend, ooff, osz]; rw [hwstk_len1]; exact Nat.le_trans hbd_ot hwlen_le1
        have hoend_cap : oend ≤ c.wcap := hwstk_len1 ▸ hoend_le
        have hoend_lt64 : oend < 2 ^ 64 := by have := hoend_cap; omega
        have h2ot0_bd_c0 : (ot_c0.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length :=
          hot_c0_eq ▸ h2ot0_bd
        have h2ot1_bd_c0 : (ot_c0.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            s1.core.wvec.length := hot_c0_eq ▸ h2ot1_bd
        have hooff_c0_eq : s1.core.wvec[(ot_c0.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd_c0 =
            s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat)).toNat]'h2ot0_bd :=
          m6_getElem_congr (by rw [hot_c0_eq]) h2ot0_bd_c0 h2ot0_bd
        have hosz_c0_eq : s1.core.wvec[(ot_c0.setWidth 64 <<< (1 : Nat) +
              (1 : BitVec 64)).toNat]'h2ot1_bd_c0 =
            s1.core.wvec[(ot.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2ot1_bd :=
          m6_getElem_congr (by rw [hot_c0_eq]) h2ot1_bd_c0 h2ot1_bd
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () mc =>
            ∃ sC2 : FullState, S13ElsLitLoop c F0 F_cur s sC2 ∧ (FullMem c sC2 ⋆ R) mc)
          (fun _ () mc ⟨sC2, hLC2, hm2⟩ => by c0_hsteps!; exact hJc () mc ⟨sC2, hLC2, hm2⟩) ?_
        intro Jc2 hJc2; c0_hsplit; rotate_left
        · c0_hsteps!; exact hJc2 () _ ⟨s1, ⟨hinv1, hcv1_eq, hs1_def.symm ▸ hLoop.fuel,
            hs1_def.symm ▸ hLoop.repr, hs1_def.symm ▸ hLoop.tmk, hs1_def.symm ▸ hLoop.trh,
            hs1_def.symm ▸ hLoop.scr, hs1_def.symm ▸ hLoop.ws1, hs1_def.symm ▸ hLoop.ws2,
            hs1_def.symm ▸ hLoop.gu⟩, hpop1_m⟩
        have hosz_pos : 0 < osz := by
          repeat rw [m6_getElem_eq_getD s1.core.wvec (d := 0#32)] at hc
          repeat rw [m6_getElem_eq_getD sL.core.wstk (d := 0#32)] at hc
          rw [hwv0_eq, @List.getElem?_eq_getElem _ sL.core.wstk offL hoffL_lt,
            Option.getD_some, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
            show BitVec.toNat 1 = 1 from rfl, Nat.mod_eq_of_lt (by omega),
            @List.getElem?_eq_getElem _ s1.core.wvec (2 * ot.toNat + 1) h2ot1_wvec,
            Option.getD_some] at hc
          unfold osz fullWatchSize fullWatchSizeCore; rw [@List.getElem?_eq_getElem _ s1.core.wvec
            (2 * ot.toNat + 1) h2ot1_wvec, Option.getD_some]; exact hc
        c0_hsteps_nogrp; dsimp only [Prod.fst]
        refine s13_els_compact_ot_watches (ot := ot_c0) hinv1 (hot_c0_eq.symm ▸ hot_lt1)
          (hot_c0_eq.symm ▸ hosz_pos) ?_ ?_ hpop1_m ?_
        · apply BitVec.eq_of_toNat_eq
          rw [hooff_c0_eq, hooff_bv, hot_c0_eq, BitVec.toNat_ofNat]
          exact (Nat.mod_eq_of_lt (by omega)).symm
        · apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, hooff_c0_eq, hosz_c0_eq, hooff_bv, hosz_bv, hot_c0_eq,
            BitVec.toNat_ofNat]
        · intro _ _ _ _ mf hinv2 hmf
          exact hJc2 () mf ⟨_, ⟨hinv2, hcv1_eq, hs1_def.symm ▸ hLoop.fuel,
            hs1_def.symm ▸ hLoop.repr, hs1_def.symm ▸ hLoop.tmk, hs1_def.symm ▸ hLoop.trh,
            hs1_def.symm ▸ hLoop.scr, hs1_def.symm ▸ hLoop.ws1, hs1_def.symm ▸ hLoop.ws2,
            hs1_def.symm ▸ hLoop.gu⟩, hmf⟩
    · have hw0_some : sL.core.wstk[offL]? = some (sL.core.wstk[offL]'hoffL_lt) :=
        List.getElem?_eq_getElem hoffL_lt
      have hw0_occ : (sL.core.wstk[offL]'hoffL_lt &&& 0x80000000#32) = 0#32 := by
        have hc0 : (sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32 := by
          first
          | exact ‹(sL.core.wstk[offL]'hoffL_lt &&& (2147483648 : BitVec 32)) = 0#32›
          | (have hh := ‹sL.core.wstk[(BitVec.setWidth 64
                (sL.core.wvec[(BitVec.setWidth 64 l <<< 1).toNat]'(by
                  rw [h2l0_c0, hclL.wvec_len]; omega))).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hw0_c0_eq] at hh)
          | (have hh := ‹sL.core.wstk[(sL.core.wvec[(2 * l.toNat) % 2 ^ 64]'(by
                rw [h2l0_mod]; exact h2l0_bdL)).toNat] &&&
                (2147483648 : BitVec 32) = 0#32›
             rwa [hwv0_eq] at hh)
        simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hc0
      obtain ⟨hsz2, _, cr, hw1_some, _, hcr_ref, hsl_nxt⟩ :=
        s13_denseSlice_step_occ hslice_l hsz_pos hw0_some hw0_occ
      c0_hsplit
      · exfalso
        have hlt2 : (sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
            rw [h2l_mod]; exact h2l_bdL)).toNat < 2 := by
          have : sL.core.wvec[(2 * l.toNat + 1) % 2 ^ 64].toNat < (2#32).toNat := by assumption
          exact this
        rw [m6_getElem_congr h2l_mod (by rw [h2l_mod]; exact h2l_bdL) h2l_bdL] at hlt2
        have hszL_eq : (sL.core.wvec[2 * l.toNat + 1]'h2l_bdL).toNat = szL := by
          unfold szL fullWatchSize fullWatchSizeCore
          rw [List.getElem?_eq_getElem h2l_bdL, Option.getD_some]
        omega
      · have hsz2_l : 2 ≤ szL := by omega
        have hoff1_lt : offL + 1 < sL.core.wstk.length := by
          have := hclL.wstk_len_arr; have := hclL.wlen_le; rw [hoff_def]; omega
        have hcr_eq : sL.core.wstk[offL + 1]'hoff1_lt = cr := by
          have hq := hw1_some; rw [List.getElem?_eq_getElem hoff1_lt] at hq
          exact Option.some.inj hq
        let wvec1 := (sL.core.wvec.set (2 * l.toNat) (BitVec.ofNat 32 (offL + 2))).set
          (2 * l.toNat + 1) (BitVec.ofNat 32 (szL - 2))
        let s1 : FullState := { sL with core := { sL.core with
          wvec := wvec1, wusable := sL.core.wusable + 2#64 } }
        have hinv1 := m6_denseInvW_watchPop hinvL hl_ltL hsz2 (sL.core.wusable + 2#64) hsl_nxt
        have hrepr1 : FullCongReprInv F_cur (2 * s1.core.cur_vars) s1.core.repr := hLoop.repr
        have hsz_lt32 : szL < 2 ^ 32 := by
          unfold szL fullWatchSize fullWatchSizeCore; exact BitVec.isLt _
        have hwv_pop2 := s13_els_wvec_pop_eq (k := 2) sL l hsz2_l (by decide) (by omega) hsz_lt32
          h2l0_c0 h2l1_c0 hoffL_bv hszL_bv
        have hws_off1_lt : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) + (1 : BitVec 64)).toNat <
            sL.core.wstk.length := by
          rw [BitVec.toNat_add, hoffL_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]; exact hoff1_lt
        have hoff1_c0 : (BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) +
            (1 : BitVec 64)).toNat = offL + 1 := by
          rw [BitVec.toNat_add, hoffL_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hcr_c0_eq : sL.core.wstk[(BitVec.setWidth 64 (sL.core.wvec[(BitVec.setWidth 64 l <<<
            (1 : Nat)).toNat]'(by rw [h2l0_c0, hclL.wvec_len]; omega)) +
            (1 : BitVec 64)).toNat]'hws_off1_lt = cr := by
          rw [m6_getElem_congr hoff1_c0 hws_off1_lt hoff1_lt]; exact hcr_eq
        dsimp only [Prod.fst]; c0_hsteps_nogrp; c0_call hElsAr
        refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hcr_c0_eq.symm ▸ hcr_eq ▸ hcr_ref,
          (by rw [show s1.core.cur_vars = s.core.cur_vars from hLoop.cv]; exact hrl_lt),
          hrepr1, ?_, ?_⟩
        · dsimp only [s1, wvec1]; rw [← hwv_pop2]; assumption
        intro okA sA mA hinvA hcvA hflA hrpA htmkA htrhA hscrA hws1A hws2A hguA hokfA hmA
        have hrpA' : FullCongReprInv F_cur (2 * sA.core.cur_vars) sA.core.repr := by
          rw [hcvA]; exact hrpA
        c0_hsplit
        · c0_hsteps!; exact hL (gL - 1#64, sA) mA (by dsimp only; omega)
            ⟨⟨hinvA, hcvA.trans hLoop.cv, hflA.trans hLoop.fuel, hrpA',
              htmkA.trans hLoop.tmk, htrhA.trans hLoop.trh, hscrA.trans hLoop.scr,
              hws1A.trans hLoop.ws1, hws2A.trans hLoop.ws2, hguA.trans hLoop.gu⟩, hmA⟩
        · have hokf : okA = false := by
            cases okA <;> first | rfl | contradiction | exact absurd rfl ‹_›
          c0_hsteps!; exact hQ false sA mA hinvA (hcvA.trans hLoop.cv) (hflA.trans hLoop.fuel)
            (by rw [← hLoop.cv]; exact hrpA) (htmkA.trans hLoop.tmk) (htrhA.trans hLoop.trh)
            (hscrA.trans hLoop.scr) (hws1A.trans hLoop.ws1) (hws2A.trans hLoop.ws2)
            (hguA.trans hLoop.gu) (fun _ => hokfA hokf) hmA
  · intro B L hB hL; c0_hsteps!
    have h2l_c0 : (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat =
        2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, m6_els_bv64_shl1_nat, bv_c0_zext32_64,
        show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [m6_getElem_congr h2l_c0 (by rw [h2l_c0]; exact h2l_bd) h2l_bd,
      ← @Option.getD_some _ (s.core.wvec[2 * l.toNat + 1]'h2l_bd) 0#32,
      ← List.getElem?_eq_getElem h2l_bd]
    exact hL (s.core.wvec[2 * l.toNat + 1]?.getD 0#32 |>.setWidth 64, s) m
      ⟨⟨hinv, rfl, rfl, hrepr_inv, rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
