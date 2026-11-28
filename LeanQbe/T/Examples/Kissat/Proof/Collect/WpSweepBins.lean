/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Watch-Stack Binary Sweep & Dedup WP Proofs (`Proof.Collect.WpSweepBins`)

Canonical `Func.wp` proofs for `full_sweep_bins_range_m6`, `full_sweep_bins_m6cf`, and
`full_sweep_bins` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Collect.M6Tactics1

public section

private theorem collect_fwd0_sb {Q : Post []} : (fun (_ : Tup Val []) m' => Q () m') = Q :=
  funext fun r => by cases r; rfl

private theorem full_mem_eq_cast {c : FullCfg} {s s' : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (heq : s = s') : (FullMem c s' ⋆ R) m :=
  heq ▸ hm

private theorem bv64_shl1_nat_eq {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

private theorem full_sweep_bins_lit_hdr_facts {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {l : BitVec 64}
    (hlen : k.LengthsOk c) (hwat : ModeWatchesInv F_cur k)
    (hcv_le : k.cur_vars ≤ c.max_vars) (hmax_lt : c.max_vars < 2 * 2 ^ 28)
    (hl_lt : l.toNat < 2 * k.cur_vars) :
    2 * l.toNat < k.wvec.length ∧ 2 * l.toNat + 1 < k.wvec.length ∧
    (l + 1#64).toNat = l.toNat + 1 ∧
    2 * l.toNat % 2 ^ 64 = 2 * l.toNat ∧
    (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 ∧
    fullWatchOffCore k l.toNat + fullWatchSizeCore k l.toNat ≤ k.wlen ∧
    ModeWatchSliceOk (decide (k.dense_mode ≠ 0#64)) F_cur k l.toNat
      (fullWatchOffCore k l.toNat) (fullWatchSizeCore k l.toNat) := by
  have hwv_len : k.wvec.length = 4 * c.max_vars := hlen.wvec_len
  refine ⟨by omega, by omega, bv64_add1 (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    hwat.bounds l.toNat hl_lt, modeWatchesInv_slice_of_lt hwat hl_lt⟩

/-! ## 1. `full_sweep_bins_range_m6_wp` Helpers -/

private theorem full_sweep_bins_range_finish_lit {c : FullCfg} {F_cur : List (List Nat)}
    {keep : Nat} {kL : FullCoreState} {sc : FullScratch} {wstk1 wstk2 : List (BitVec 32)}
    {wu' nb1 : BitVec 64} {l q_nat : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hdkp : 0 < keep → kL.dense_mode = 0#64)
    (hwatL : ModeWatchesInv F_cur kL)
    (hltL : ∀ j < l, WatchSliceLtOk keep F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hlen2 : wstk2.length = c.wcap)
    (hoq : fullWatchOffCore kL l ≤ q_nat)
    (hqe : q_nat ≤ fullWatchOffCore kL l + fullWatchSizeCore kL l)
    (hout1 : ∀ i, i < fullWatchOffCore kL l ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk1[i]? = kL.wstk[i]?)
    (hout2 : ∀ i, i < q_nat ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk2[i]? = wstk1[i]?)
    (hpre1 : WatchSliceLtOk keep F_cur { kL with wstk := wstk1 } l (fullWatchOffCore kL l)
      (q_nat - fullWatchOffCore kL l))
    (kL' : FullCoreState)
    (hk' : kL' = { kL with wvec := kL.wvec.set (2 * l + 1)
                                     (BitVec.ofNat 32 (q_nat - fullWatchOffCore kL l)),
                           wstk := wstk2, wusable := wu', num_binary := nb1 }) :
    FullState.LengthsOk c ⟨kL', sc⟩ ∧ ModeWatchesInv F_cur kL' ∧
    ∀ j < l + 1, WatchSliceLtOk keep F_cur kL' j (fullWatchOffCore kL' j)
      (fullWatchSizeCore kL' j) := by
  subst hk'
  let off0 := fullWatchOffCore kL l; let sz0 := fullWatchSizeCore kL l
  let wvec' := kL.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q_nat - off0))
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = kL.wstk[i]? :=
    fun i hi => by rw [hout2 i (by omega), hout1 i (by omega)]
  have hlt_l : WatchSliceLtOk keep F_cur { kL with wstk := wstk2 } l off0 (q_nat - off0) :=
    WatchSliceLtOk.relocate (k := { kL with wstk := wstk1 }) (k' := { kL with wstk := wstk2 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr _ => hr) (fun j hj => hout2 (off0 + j) (Or.inl (by omega))) hpre1
  have hmode_l : ModeWatchSliceOk (decide (kL.dense_mode ≠ 0#64)) F_cur { kL with wstk := wstk2 }
      l off0 (q_nat - off0) := by
    by_cases hd : decide (kL.dense_mode ≠ 0#64) = true
    · simp only [ModeWatchSliceOk, hd, ↓reduceIte]
      by_cases hkz : keep = 0
      · subst hkz; exact (WatchSliceLtOk.toBinOnly hlt_l).toDenseWatchSliceOk
      · exfalso; have h0 := hdkp (Nat.pos_of_ne_zero hkz); simp [h0] at hd
    · simp only [ModeWatchSliceOk, hd, Bool.false_eq_true, ↓reduceIte]; exact hlt_l.toWatchSliceOk
  have hwat' := modeWatchesInv_shrink_slice hwatL hlenL hl_lt (new_sz := q_nat - off0) (by omega)
    hout_fin wu' nb1 hmode_l
  obtain ⟨_, hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hwatL.layout hlenL hl_lt
      (new_sz := q_nat - off0) (by omega) hout_fin hlt_l.ne_sentinel wu' nb1
  refine ⟨⟨{ hlenL with wvec_len := by simp [hlenL.wvec_len],
                        wstk_len_arr := hlen2 }, hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst j; rw [hoff_self, hsz_self]
    exact WatchSliceLtOk.relocate (k := { kL with wstk := wstk2 })
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p)
      (Nat.le_refl _) (fun _ hr _ => hr) (fun _ _ => rfl) hlt_l
  · obtain ⟨ho, hs, hws⟩ := hother j (by omega) hjl; rw [ho, hs]
    exact WatchSliceLtOk.relocate (k := kL)
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr _ => hr) hws (hltL j (by omega))

private abbrev sweepBinState (s : FullState) (wvecL wstk1 : List (BitVec 32))
    (wuL nb1 : BitVec 64) (ws1 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nb1 }
    scratch := { s.scratch with wsort := ws1 } }

private def SweepBinPInv (c : FullCfg) (F_cur : List (List Nat)) (s sL : FullState)
    (R : Mem 64 → Prop) (dense : Bool) (keep_before : Nat)
    (l : BitVec 64) (off0 end0 : Nat) (wvecL wstkL : List (BitVec 32)) (wuL nbL : BitVec 64)
    (arg : Tup Val [i64, i64]) (m1 : Mem 64) : Prop :=
  let (p, q, ()) := arg
  off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
  ∃ wstk1 nb1 ws1, wstk1.length = c.wcap ∧ ws1.length = 2 * c.max_vars ∧
    (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
    ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat (end0 - p.toNat) ∧
    WatchSliceLtOk keep_before F_cur
      (sweepBinState s wvecL wstk1 wuL nbL ws1).core l.toNat off0 (q.toNat - off0) ∧
    (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 ws1) ⋆ R) m1

private def SweepBinQInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (keep_before : Nat) (l : BitVec 64) (off0 pend : Nat)
    (wvecL wstkL : List (BitVec 32)) (wuL nbL : BitVec 64)
    (arg : Tup Val [i64]) (mQ : Mem 64) : Prop :=
  let (q', ()) := arg
  off0 ≤ q'.toNat ∧ q'.toNat ≤ pend ∧
  ∃ wstk' nb' ws', wstk'.length = c.wcap ∧ ws'.length = 2 * c.max_vars ∧
    (∀ i, i < off0 ∨ pend ≤ i → wstk'[i]? = wstkL[i]?) ∧
    WatchSliceLtOk keep_before F_cur
      (sweepBinState s wvecL wstk' wuL nbL ws').core l.toNat off0 (q'.toNat - off0) ∧
    (FullMem c (sweepBinState s wvecL wstk' wuL nb' ws') ⋆ R) mQ

private abbrev lfixOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  Op.mk code (a, ())

private abbrev lfixOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  Op.mk code (a, b, ())

open Lean Elab Tactic in
local elab "lfix_steps" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      if e.isAppOf ``LeanQbe.T.Expr.load || e.isAppOf ``LeanQbe.T.Expr.jnz then break
    let _ ← evalTactic (← `(tactic| repeat m6_strip))
    if !(← LeanQbe.T.C0Step.stepOnce) then break

private abbrev lfixValsTail {rs : List Ty} (J : Cont [Ty.bool]) (pVals l : Val i64)
    (pd : Val Ty.bool) : Expr Val Cont rs :=
  Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var l)) fun p =>
    Expr.load i8 (Arg.var p.fst) fun ld =>
      Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
        Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
            Expr.let_ (lfixOp2 (.cmp .sgt i32 .bool (by decide)) (Arg.var p_1.fst) (Arg.var p.fst))
              fun p =>
              Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                (Expr.jnz (Arg.var pd)
                  (Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var l)) fun p =>
                    Expr.load i8 (Arg.var p.fst) fun ld =>
                      Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
                        Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
                          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
                            Expr.let_ (lfixOp2 (.cmp .slt i32 .bool (by decide))
                              (Arg.var p_1.fst) (Arg.var p.fst)) fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                                (Expr.jump (J, ()).fst (Arg.imm false, ())))
                  (Expr.jump (J, ()).fst (Arg.imm false, ())))

private theorem sweep_bins_vals_tail_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pVals l : Val i64} {pd : Val Ty.bool} {valV : BitVec 8}
    (J : Cont [Ty.bool]) (h2 : loadVal m i8 (pVals + l) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X (lfixValsTail J pVals l pd) m := by
  unfold lfixValsTail
  lfix_steps; rw [wp_load]; refine ⟨valV, h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true) (fun _ => ?_)
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨valV, h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true)
    (fun _ => by lfix_steps; exact hJ false)

private theorem sweep_bins_lfix_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pLvl pVals l : Val i64} {pd : Val Ty.bool} {lvlV : BitVec 32}
    {valV : BitVec 8} (J : Cont [Ty.bool])
    (h1 : loadVal m i32 (pLvl + (l >>> (1 : Nat)) * 4#64) = some lvlV)
    (h2 : loadVal m i8 (pVals + l) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X
      (Expr.let_ (lfixOp1 (.sext 32 64) (Arg.imm 1)) fun p =>
        Expr.let_ (lfixOp2 (.lshr i64) (Arg.var l) (Arg.var p.fst)) fun p =>
          Expr.let_ (lfixOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4)) fun p =>
            Expr.let_ (lfixOp2 (.add i64) (Arg.var pLvl) (Arg.var p.fst)) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_ (lfixOp2 (.cmp .eq i32 .bool (by decide)) (Arg.var ld) (Arg.imm 0))
                  fun p =>
                  Expr.jnz (Arg.var p.fst) (lfixValsTail J pVals l pd)
                    (Expr.jump (J, ()).fst (Arg.imm false, ()))) m := by
  lfix_steps; rw [wp_load]; refine ⟨lvlV, ?_, ?_⟩
  · simpa [BitVec.ushiftRight] using h1
  · lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
    · exact sweep_bins_vals_tail_wp J h2 hJ
    · lfix_steps; exact hJ false

private abbrev ofixValsTail {rs : List Ty} (J : Cont [Ty.bool]) (pVals : Val i64) (ot : Val i32)
    (pd : Val Ty.bool) : Expr Val Cont rs :=
  Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
    Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var p.fst)) fun p =>
      Expr.load i8 (Arg.var p.fst) fun ld =>
        Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
            Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
              Expr.let_ (lfixOp2 (.cmp .sgt i32 .bool (by decide)) (Arg.var p_1.fst)
                (Arg.var p.fst)) fun p =>
                Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                  (Expr.jnz (Arg.var pd)
                    (Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
                      Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var p.fst)) fun p =>
                        Expr.load i8 (Arg.var p.fst) fun ld =>
                          Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
                            Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
                              Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
                                Expr.let_ (lfixOp2 (.cmp .slt i32 .bool (by decide))
                                  (Arg.var p_1.fst) (Arg.var p.fst)) fun p =>
                                  Expr.jnz (Arg.var p.fst)
                                    (Expr.jump (J, ()).fst (Arg.imm true, ()))
                                    (Expr.jump (J, ()).fst (Arg.imm false, ())))
                    (Expr.jump (J, ()).fst (Arg.imm false, ())))

private theorem sweep_bins_ofix_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pLvl pVals nlits : Val i64} {ot : Val i32} {pd : Val Ty.bool}
    {lvlV : BitVec 32} {valV : BitVec 8} (J : Cont [Ty.bool])
    (h1 : loadVal m i32 (pLvl + (ot.setWidth 64 >>> (1 : Nat)) * 4#64) = some lvlV)
    (h2 : loadVal m i8 (pVals + ot.setWidth 64) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X
      (Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
        Expr.let_ (lfixOp2 (.cmp .ult i64 .bool (by decide)) (Arg.var p.fst) (Arg.var nlits))
          fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.let_ (lfixOp2 (.lshr i32) (Arg.var ot) (Arg.imm 1)) fun p =>
              Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var p.fst)) fun p =>
                Expr.let_ (lfixOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4)) fun p =>
                  Expr.let_ (lfixOp2 (.add i64) (Arg.var pLvl) (Arg.var p.fst)) fun p =>
                    Expr.load i32 (Arg.var p.fst) fun ld =>
                      Expr.let_ (lfixOp2 (.cmp .eq i32 .bool (by decide)) (Arg.var ld)
                        (Arg.imm 0)) fun p =>
                        Expr.jnz (Arg.var p.fst) (ofixValsTail J pVals ot pd)
                          (Expr.jump (J, ()).fst (Arg.imm false, ())))
            (Expr.jump (J, ()).fst (Arg.imm false, ()))) m := by
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨lvlV, ?_, ?_⟩
  · simpa [BitVec.ushiftRight, BitVec.setWidth_ushiftRight] using h1
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  unfold ofixValsTail
  lfix_steps; rw [wp_load]; refine ⟨valV, by simpa using h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true) (fun _ => ?_)
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨valV, by simpa using h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true)
    (fun _ => by lfix_steps; exact hJ false)

private theorem sweep_bins_range_bin_keep {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {keep : Nat} {l q : BitVec 64} {off0 p_nat : Nat}
    {wvecL wstk1 wstkL : List (BitVec 32)} {wuL nbL : BitVec 64} {ws1 : List (BitVec 32)}
    {w0 : BitVec 32} (_ : wstk1.length = c.wcap) (hoq : off0 ≤ q.toNat)
    (hqp : q.toNat ≤ p_nat) (hq_w : q.toNat < wstk1.length)
    (hout1 : ∀ i, i < off0 ∨ p_nat ≤ i → wstk1[i]? = wstkL[i]?)
    (hpre1 : WatchSliceLtOk keep F_cur (sweepBinState s wvecL wstk1 wuL nbL ws1).core
      l.toNat off0 (q.toNat - off0))
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt_o : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hent_o : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [l.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hq1_eq : (q + 1#64).toNat = q.toNat + 1) :
    (∀ i, i < off0 ∨ p_nat + 1 ≤ i → (wstk1.set q.toNat w0)[i]? = wstkL[i]?) ∧
    WatchSliceLtOk keep F_cur (sweepBinState s wvecL (wstk1.set q.toNat w0) wuL nbL ws1).core
      l.toNat off0 ((q + 1#64).toNat - off0) := by
  refine ⟨fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega), ?_⟩
  rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
  exact WatchSliceLtOk.append_bin
    (k := (sweepBinState s wvecL wstk1 wuL nbL ws1).core)
    (k' := (sweepBinState s wvecL (wstk1.set q.toNat w0) wuL nbL ws1).core)
    (p := off0) (p' := off0) (Nat.le_refl _) (fun _ hr _ => hr)
    (fun j hj => List.getElem?_set_ne (by omega)) hpre1
    (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]; exact List.getElem?_set_self hq_w)
    hbin hne hlt_o hent_o

private theorem sweep_bins_range_large_keep {F_cur : List (List Nat)} {s : FullState}
    {keep : Nat} {l q : BitVec 64} {off0 p_nat : Nat}
    {wvecL wstk1 wstkL : List (BitVec 32)} {wuL nbL : BitVec 64} {ws1 : List (BitVec 32)}
    {w0 cr : BitVec 32} (hoq : off0 ≤ q.toNat) (hqp : q.toNat ≤ p_nat)
    (hq_w : q.toNat < wstk1.length) (hq1_lt : q.toNat + 1 < (wstk1.set q.toNat w0).length)
    (hout1 : ∀ i, i < off0 ∨ p_nat ≤ i → wstk1[i]? = wstkL[i]?)
    (hpre1 : WatchSliceLtOk keep F_cur (sweepBinState s wvecL wstk1 wuL nbL ws1).core
      l.toNat off0 (q.toNat - off0))
    (hlg : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cr.toNat < 0x80000000) (hkp : cr.toNat < keep)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore
      (sweepBinState s wvecL wstk1 wuL nbL ws1).core)
    (hq2_eq : (q + 2#64).toNat = q.toNat + 2) :
    let wstk2 := (wstk1.set q.toNat w0).set (q.toNat + 1) cr
    (∀ i, i < off0 ∨ p_nat + 2 ≤ i → wstk2[i]? = wstkL[i]?) ∧
    WatchSliceLtOk keep F_cur (sweepBinState s wvecL wstk2 wuL nbL ws1).core
      l.toNat off0 ((q + 2#64).toNat - off0) := by
  intro wstk2
  refine ⟨fun i hi => by
    dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout1 i (by omega), ?_⟩
  rw [hq2_eq, show q.toNat + 2 - off0 = (q.toNat - off0) + 2 by omega]
  exact WatchSliceLtOk.append_large
    (k := (sweepBinState s wvecL wstk1 wuL nbL ws1).core)
    (k' := (sweepBinState s wvecL wstk2 wuL nbL ws1).core)
    (p := off0) (p' := off0) (Nat.le_refl _) (fun _ hr _ => hr)
    (fun j hj => by dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)])
    hpre1 (by dsimp only [wstk2]; rw [show off0 + (q.toNat - off0) = q.toNat by omega,
      List.getElem?_set_ne (by omega), List.getElem?_set_self hq_w])
    (by dsimp only [wstk2]; rw [show off0 + (q.toNat - off0) + 1 = q.toNat + 1 by omega,
      List.getElem?_set_self hq1_lt])
    hlg hcr_lt hkp hcr_ref

private theorem sweep_bins_range_exit_lit {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {keep : Nat} {l q : BitVec 64} {offW szW : BitVec 32}
    {wvecL wstkL wstk1 wstk2 : List (BitVec 32)} {wuL nbL nb1 : BitVec 64}
    {ws1 : List (BitVec 32)} (hws1 : ws1.length = 2 * c.max_vars)
    (hlenL : (sweepBinState s wvecL wstkL wuL nbL ws1).LengthsOk c)
    (hdkp : 0 < keep → s.core.dense_mode = 0#64)
    (hwatL : ModeWatchesInv F_cur (sweepBinState s wvecL wstkL wuL nbL ws1).core)
    (hltL : ∀ j < l.toNat, WatchSliceLtOk keep F_cur
      (sweepBinState s wvecL wstkL wuL nbL ws1).core j
      (fullWatchOff (sweepBinState s wvecL wstkL wuL nbL ws1) j)
      (fullWatchSize (sweepBinState s wvecL wstkL wuL nbL ws1) j))
    (hl_lt : l.toNat < 2 * s.core.cur_vars)
    (hlen2 : wstk2.length = c.wcap)
    (hoff_eq : offW.toNat = fullWatchOff (sweepBinState s wvecL wstkL wuL nbL ws1) l.toNat)
    (hsz_eq : szW.toNat = fullWatchSize (sweepBinState s wvecL wstkL wuL nbL ws1) l.toNat)
    (h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1)
    (hoq : offW.toNat ≤ q.toNat) (hqp : q.toNat ≤ offW.toNat + szW.toNat)
    (hout1 : ∀ i, i < offW.toNat ∨ offW.toNat + szW.toNat ≤ i → wstk1[i]? = wstkL[i]?)
    (hout2 : ∀ i, i < q.toNat ∨ offW.toNat + szW.toNat ≤ i → wstk2[i]? = wstk1[i]?)
    (hpre1 : WatchSliceLtOk keep F_cur (sweepBinState s wvecL wstk1 wuL nbL ws1).core l.toNat
      offW.toNat (q.toNat - offW.toNat))
    :
    let qbv := (q - offW.setWidth 64).setWidth 32
    let wvec' := wvecL.set ((l <<< (1 : Nat)) + 1#64).toNat qbv
    let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
    let sF := sweepBinState s wvec' wstk2 wu' nb1 ws1
    qbv = BitVec.ofNat 32 (q.toNat - offW.toNat) ∧
    sF.LengthsOk c ∧ ModeWatchesInv F_cur sF.core ∧
    ∀ j < l.toNat + 1,
      WatchSliceLtOk keep F_cur sF.core j (fullWatchOff sF j) (fullWatchSize sF j) := by
  intro qbv wvec' wu' sF
  have hlt32 : q.toNat - offW.toNat < 2 ^ 32 := by omega
  have hqbv : qbv = BitVec.ofNat 32 (q.toNat - offW.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    have : (2 ^ 64 - offW.toNat + q.toNat) % 2 ^ 64 = q.toNat - offW.toNat := by omega
    rw [this, Nat.mod_eq_of_lt hlt32]
  have hwvec_eq : wvec' = wvecL.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat -
      fullWatchOffCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat)) := by
    dsimp only [wvec']; rw [h2l1_eq, hqbv, hoff_eq]
  unfold fullWatchOff at hoff_eq
  unfold fullWatchSize at hsz_eq
  have hout1' : ∀ i, i < fullWatchOffCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat ∨
      fullWatchOffCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat +
      fullWatchSizeCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat ≤ i →
      wstk1[i]? = wstkL[i]? := by rw [← hoff_eq, ← hsz_eq]; exact hout1
  have hout2' : ∀ i, i < q.toNat ∨
      fullWatchOffCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat +
      fullWatchSizeCore (sweepBinState s wvecL wstkL wuL nbL ws1).core l.toNat ≤ i →
      wstk2[i]? = wstk1[i]? := by rw [← hoff_eq, ← hsz_eq]; exact hout2
  have hfin := full_sweep_bins_range_finish_lit (F_cur := F_cur)
    (kL := (sweepBinState s wvecL wstkL wuL nbL ws1).core) (wstk1 := wstk1) (wstk2 := wstk2)
    (keep := keep) hlenL.core_ok hlenL.scratch_ok hdkp hwatL hltL hl_lt hlen2
    (by rw [← hoff_eq]; exact hoq) (by rw [← hoff_eq, ← hsz_eq]; exact hqp)
    hout1' hout2' (by rw [← hoff_eq]; exact hpre1) sF.core (by
      change { sF.core with } = _; dsimp only [sF, sweepBinState]; rw [hwvec_eq])
  refine ⟨hqbv, ⟨hfin.1.core_ok, { hlenL.scratch_ok with wsort_len := hws1 }⟩,
    hfin.2.1, hfin.2.2⟩

theorem full_sweep_bins_range_m6_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Func.wp Γ full_sweep_bins_range_m6_body a m Q X := by
  rintro ⟨h, keep_before, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hdkp, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le; have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len; have hl_len := hlen.core_ok.lvl_len
  have hwsrt_len := hlen.scratch_ok.wsort_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [bv64_shl1_nat_eq (by rw [bv64_ofNat_toNat_id (by omega)]; omega),
      bv64_ofNat_toNat_id (by omega)]
  m6_to_group
  refine wp_loop_inv
    (fun (s0, ()) m0 => s0.toNat ≤ 2 * s.core.cur_vars ∧ ∃ ws0 : List (BitVec 32),
      ws0.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with wsort := ws0 } } ⋆ R) m0)
    (fun (s0, ()) _ => 2 * s.core.cur_vars - s0.toNat) (fun J0 hLoop0 => ?_) ?_
  · m6_steps; exact hLoop0 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort, hwsrt_len, hm⟩
  · rintro J0 ⟨s0, ⟨⟩⟩ m0 ⟨hs0_le, ws0, hws0, hm0⟩ hLoop0
    clear hm; m6_split_fast
    · have hs0_lt : s0.toNat < 2 * s.core.cur_vars := by
        have : s0.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hs0p1 : (s0 + 1#64).toNat = s0.toNat + 1 := bv64_add1 (by omega)
      m6_c0_steps
      exact hLoop0 (s0 + 1#64, ()) _ (by dsimp only; rw [hs0p1]; omega)
        ⟨by rw [hs0p1]; omega, ws0.set s0.toNat 0xFFFFFFFF#32, by simp [hws0], hm⟩
    · have hs0_eq : s0.toNat = 2 * s.core.cur_vars := by
        have : ¬ (s0.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat) := by
          c0_bound
        omega
      clear hc J0 hLoop0 s0 hs0_le hs0_eq
      m6_c0_steps
      refine wp_loop_inv
        (fun (l, ()) mL =>
          l.toNat ≤ 2 * s.core.cur_vars ∧
          ∃ wvecL wstkL wuL nbL wsL,
            let sL := sweepBinState s wvecL wstkL wuL nbL wsL
            sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
            (∀ j < l.toNat, WatchSliceLtOk keep_before.toNat F_cur sL.core j
                (fullWatchOff sL j) (fullWatchSize sL j)) ∧
            (FullMem c sL ⋆ R) mL)
        (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat) (fun JL hLoopL => ?_) ?_
      · m6_c0_steps
        exact hLoopL (0#64, ()) m0 ⟨Nat.zero_le _, s.core.wvec, s.core.wstk, s.core.wusable,
          s.core.num_binary, ws0, ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hws0 }⟩,
          hw.watches, fun _ hj => absurd hj (Nat.not_lt_zero _), hm0⟩
      · rintro JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, wsL, hlenL, hwatL, hltL, hmL⟩ hLoopL
        let sL := sweepBinState s wvecL wstkL wuL nbL wsL
        have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
        have hwsL_len : wsL.length = 2 * c.max_vars := hlenL.scratch_ok.wsort_len
        m6_split_fast
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
            have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
            omega
          obtain ⟨h2l_lt, h2l1_lt, hl1_eq, hmod0, hmod1, hbd_end, hslice0⟩ :=
            full_sweep_bins_lit_hdr_facts hlenL.core_ok hwatL hcv_le hmax_lt hl_lt
          have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_nat_eq (by omega)
          have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
            rw [BitVec.toNat_add, h2l_eq, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          let off0 : Nat := fullWatchOff sL l.toNat; let sz0 : Nat := fullWatchSize sL l.toNat
          let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
          let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega)
          have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
            unfold off0 fullWatchOff fullWatchOffCore sL sweepBinState
            rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
          have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
            unfold sz0 fullWatchSize fullWatchSizeCore sL sweepBinState
            rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
          have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
          have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
          have h1bv : (1 : BitVec 64).toNat = 1 := rfl
          clear hw hlen hm0 hdefrag hQ
          m6_split_fast
          · have hsz0 : sz0 = 0 := by
              have h1 := congrArg BitVec.toNat hc; simp only [h1bv, hmod1] at h1
              rwa [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
            m6_c0_steps
            refine hLoopL (l + 1#64, ()) mL (by dsimp only; rw [hl1_eq]; omega)
              ⟨by rw [hl1_eq]; omega, wvecL, wstkL, wuL, nbL, wsL, hlenL, hwatL,
               fun j hj => ?_, hmL⟩
            rw [hl1_eq] at hj; by_cases hjl : j = l.toNat
            · subst hjl; change WatchSliceLtOk keep_before.toNat F_cur sL.core l.toNat off0 sz0
              rw [hsz0]; exact .empty
            · exact hltL j (by omega)
          · have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
            have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
            have hl_v : l.toNat < s.core.vals.length := by omega
            let end0 : Nat := off0 + sz0
            have hend_le : end0 ≤ c.wcap :=
              le_trans hbd_end hlenL.core_ok.wlen_le
            have hend_mod : (off0 + sz0) % 2 ^ 64 = off0 + sz0 :=
              Nat.mod_eq_of_lt (by omega)
            m6_to_group; refine wp_join_group (fun (_lfix, ()) mF => mL = mF) ?_ ?_
            · rintro _ ⟨lfix, ⟨⟩⟩ _ rfl; m6_c0_steps
              refine wp_loop_inv
                (SweepBinPInv c F_cur s sL R dense keep_before.toNat l off0 end0 wvecL wstkL
                  wuL nbL) (fun (p, _, ()) _ => end0 - p.toNat) (fun J1 hLoop1 => ?_) ?_
              · m6_c0_steps
                have hoff64 : (offW.setWidth 64).toNat = off0 := by
                  rw [zext_toNat offW (by decide), hoff_eq]
                refine hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
                  by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
                  wstkL, nbL, wsL, hlenL.core_ok.wstk_len_arr, hwsL_len, fun _ _ => rfl,
                  by rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0,
                  by rw [hoff64, Nat.sub_self]; exact .empty, hmL⟩
              · rintro J1 ⟨p, q, ⟨⟩⟩ m1 ⟨hoq, hqp, hpe, wstk1, nb1, ws1, hlen1, hws1,
                  hout1, hrem1, hpre1, hm1⟩ hLoop1
                m6_split_fast
                · have hp_lt : p.toNat < end0 := by
                    have h1 := hc
                    simp only [h1bv, hmod0, hmod1,
                      hoff_idx, hsz_idx, hend_mod] at h1
                    omega
                  have hp_w : p.toNat < wstk1.length := by omega
                  have hq_w : q.toNat < wstk1.length := by omega
                  let w0 := wstk1[p.toNat]'hp_w
                  have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
                    dsimp only [sL, sweepBinState]
                    rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
                  have hstep := hrem1.step (by omega) hw0_orig
                  m6_to_group
                  refine wp_join_group (ts := [i64, i64])
                    (fun (p', q', ()) mB => p.toNat < p'.toNat ∧ p'.toNat ≤ end0 ∧
                      off0 ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧
                      ∃ wstk' nb' ws', wstk'.length = c.wcap ∧ ws'.length = 2 * c.max_vars ∧
                        (∀ i, i < off0 ∨ p'.toNat ≤ i → wstk'[i]? = wstkL[i]?) ∧
                        ModeWatchSliceOk dense F_cur sL.core l.toNat p'.toNat (end0 - p'.toNat) ∧
                        WatchSliceLtOk keep_before.toNat F_cur
                          (sweepBinState s wvecL wstk' wuL nbL ws').core l.toNat off0
                          (q'.toNat - off0) ∧
                        (FullMem c (sweepBinState s wvecL wstk' wuL nb' ws') ⋆ R) mB) ?_ ?_
                  · rintro _ ⟨p', q', ⟨⟩⟩ mB ⟨hpp', hpe', hoq', hqp', wstk', nb', ws', hlen',
                      hws', hout', hrem'', hpre', hmB⟩
                    m6_nojoin
                    exact hLoop1 (p', q', ()) mB (by dsimp only; omega)
                      ⟨hoq', hqp', hpe', wstk', nb', ws', hlen', hws', hout', hrem'', hpre', hmB⟩
                  · intro JB hJB; m6_split_fast
                    · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                        change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
                      obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
                      have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1 (by omega)
                      have hq1_eq : (q + 1#64).toNat = q.toNat + 1 := bv64_add1 (by omega)
                      have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
                      have hot_v :
                          ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
                        rw [zext_toNat _ (by decide)]; omega
                      have hot_l : (((w0 &&& 0x7FFFFFFF#32).setWidth 64) >>> (1 : Nat)).toNat <
                          s.core.lvl.length := by
                        rw [BitVec.toNat_ushiftRight, zext_toNat _ (by decide),
                          Nat.shiftRight_eq_div_pow]; omega
                      m6_to_group
                      refine wp_join_group (fun (_ofix, ()) mO => m1 = mO) ?_ ?_
                      · rintro _ ⟨_ofix, ⟨⟩⟩ _ rfl; m6_to_group
                        refine wp_join_group (ts := [i64])
                          (SweepBinQInv c F_cur s R keep_before.toNat l off0 (p.toNat + 1)
                            wvecL wstkL wuL nbL) ?_ ?_
                        · rintro _ ⟨q', ⟨⟩⟩ mQ ⟨hoq', hqp', wstk', nb', ws', hlen', hws', hout',
                            hpre', hmQ⟩
                          m6_nojoin
                          exact hJB (p + 1#64, q', ()) mQ
                            ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hoq',
                             by rw [hp1_eq]; omega, wstk', nb', ws', hlen', hws',
                             by rw [hp1_eq]; exact hout',
                             by rw [hp1_eq,
                                  show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                                exact hrem', hpre', hmQ⟩
                        · intro Jq hJq; m6_to_group
                          refine wp_join_group (fun () mD => m1 = mD) ?_ ?_
                          · rintro _ ⟨⟩ _ rfl; m6_to_group
                            refine wp_join_group
                              (fun () mN => ∃ nb',
                                (FullMem c (sweepBinState s wvecL wstk1 wuL nb' ws1) ⋆ R) mN)
                              ?_ ?_
                            · rintro _ ⟨⟩ mN ⟨nb', hmN⟩; m6_nojoin
                              exact hJq (q, ()) mN ⟨hoq, by omega, wstk1, nb', ws1, hlen1,
                                hws1, fun i hi => hout1 i (by omega), hpre1, hmN⟩
                            · intro JN hJN; m6_split_fast
                              · m6_split_fast
                                · m6_nojoin; exact hJN () _ ⟨nb1 - 1#64, hm⟩
                                · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                              · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                          · intro Jd hJd
                            clear hLoopL JL hwatL hlenL hslice0 hrem1 hstep
                            m6_to_jnz; refine wp_jnz_of (fun _ => hJd () m1 rfl) (fun hc_nl => ?_)
                            m6_to_jnz; refine wp_jnz_of (fun _ => hJd () m1 rfl) (fun hc_no => ?_)
                            m6_to_group
                            refine wp_join_group
                              (SweepBinQInv c F_cur s R keep_before.toNat l off0 (p.toNat + 1)
                                wvecL wstkL wuL nbL) ?_ ?_
                            · rintro _ ⟨q', ⟨⟩⟩ mQ hq; m6_nojoin; exact hJq (q', ()) mQ hq
                            · intro Jq' hJq'; m6_to_jnz
                              refine wp_jnz_of (fun hc_f => ?_) (fun _ => ?_)
                              · simp only [Arg.val_var] at hc_f hc_nl
                                exfalso; cases hc_nl.symm.trans hc_f
                              · m6_to_group
                                refine wp_join_group
                                  (SweepBinQInv c F_cur s R keep_before.toNat l off0
                                    (p.toNat + 1) wvecL wstkL wuL nbL) ?_ ?_
                                · rintro _ ⟨q', ⟨⟩⟩ mQ hq; m6_nojoin; exact hJq' (q', ()) mQ hq
                                · intro Jq'' hJq''
                                  have hot_64 : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by
                                    rw [zext_toNat _ (by decide), hnlits_eq]; exact hot_lt
                                  have hot_ws : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                      ws1.length := by rw [zext_toNat _ (by decide)]; omega
                                  have h_t : (((w0 &&& 0x7FFFFFFF#32).setWidth 64).ult
                                      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat))) =
                                      true := by simpa [BitVec.ult, decide_eq_true_eq] using hot_64
                                  m6_to_jnz
                                  refine wp_jnz_of (fun _ => ?_) (fun hc_nlt => by
                                    simp only [Arg.val_var] at hc_nlt
                                    cases hc_nlt.symm.trans h_t)
                                  m6_to_jnz; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                                  · m6_to_group
                                    refine wp_join_group
                                      (fun () mN => ∃ nb', (FullMem c (sweepBinState s wvecL wstk1
                                        wuL nb' ws1) ⋆ R) mN) ?_ ?_
                                    · rintro _ ⟨⟩ mN ⟨nb', hmN⟩; m6_nojoin
                                      exact hJq'' (q, ()) mN ⟨hoq, by omega, wstk1, nb', ws1,
                                        hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hmN⟩
                                    · intro JN hJN; m6_split_fast
                                      · m6_split_fast
                                        · m6_nojoin; exact hJN () _ ⟨nb1 - 1#64, hm⟩
                                        · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                                      · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                                  · m6_to_group
                                    refine wp_join_group
                                      (fun () mS => ∃ wsS : List (BitVec 32),
                                        wsS.length = 2 * c.max_vars ∧
                                        (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 wsS) ⋆ R)
                                          mS) ?_ ?_
                                    · rintro _ ⟨⟩ mS ⟨wsS, hwsS, hmS⟩; m6_nojoin
                                      obtain ⟨hout', hpre'⟩ := sweep_bins_range_bin_keep hlen1 hoq
                                        hqp hq_w hout1 hpre1 hbin hne hlt_o hent_o hq1_eq
                                      exact hJq'' (q + 1#64, ()) _
                                        ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                                         wstk1.set q.toNat w0, nb1, wsS, by simp [hlen1], hwsS,
                                         hout', hpre', hm⟩
                                    · intro Js hJs; m6_to_jnz
                                      refine wp_jnz_of (fun _ => ?_) (fun hc_nlt2 => by
                                        simp only [Arg.val_var] at hc_nlt2
                                        cases hc_nlt2.symm.trans h_t)
                                      m6_usteps; apply wp_store_sep
                                      · exact FullArenaTactics.c0_store_full_wsort _ hot_ws hm1
                                      intro m hm; m6_nojoin
                                      exact hJs () _ ⟨_, by simp [hws1], hm⟩
                      · intro Jo hJo
                        exact sweep_bins_ofix_wp Jo
                          (@FullArenaTactics.c0_load_full_lvl c
                            (sweepBinState s wvecL wstk1 wuL nb1 ws1) R m1 _ hot_l hm1)
                          (@FullArenaTactics.c0_load_full_vals c
                            (sweepBinState s wvecL wstk1 wuL nb1 ws1) R m1 _ hot_v hm1)
                          (fun _ => hJo _ _ rfl)
                    · have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                        change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
                      obtain ⟨h2rem, cr, hcr_orig, _hsz32, hcr_lt, hcr_ref, hrem'⟩ := hstep.2 hlg
                      have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1 (by omega)
                      have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2 (by omega)
                      have hp1_lt : (p + 1#64).toNat < end0 := by omega
                      have hp1_w : (p + 1#64).toNat < wstk1.length := by omega
                      have hcr_eq : wstk1[(p + 1#64).toNat]'hp1_w = cr := by
                        have h1 := hout1 (p.toNat + 1) (Or.inr (by omega))
                        rw [List.getElem?_eq_getElem (by omega : p.toNat + 1 < wstk1.length),
                          hcr_orig] at h1
                        simpa [hp1_eq] using Option.some.inj h1
                      clear hLoopL JL hwatL hlenL hslice0 hstep
                      let invL : Tup Val [i64] → Mem 64 → Prop := fun (q', ()) mK =>
                        off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 2 ∧
                        ∃ wstk' : List (BitVec 32), wstk'.length = c.wcap ∧
                          (∀ i, i < off0 ∨ p.toNat + 2 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                          WatchSliceLtOk keep_before.toNat F_cur
                            (sweepBinState s wvecL wstk' wuL nbL ws1).core l.toNat off0
                            (q'.toNat - off0) ∧
                          (FullMem c (sweepBinState s wvecL wstk' wuL nb1 ws1) ⋆ R) mK
                      m6_to_group; refine wp_join_group (ts := [i64]) invL ?_ ?_
                      · rintro _ ⟨q', ⟨⟩⟩ mK ⟨hoq', hqp', wstk', hlen', hout', hpre', hmK⟩
                        m6_nojoin
                        exact hJB (p + 2#64, q', ()) mK
                          ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, hoq',
                           by rw [hp2_eq]; omega, wstk', nb1, ws1, hlen', hws1,
                           fun i hi => by rw [hp2_eq] at hi; exact hout' i (by omega),
                           by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                              exact hrem', hpre', hmK⟩
                      · intro Jp hJp; m6_to_jnz
                        refine wp_jnz_of (fun _ => ?_) (fun hc_np1 => ?_)
                        · m6_to_group; refine wp_join_group (ts := [i64]) invL ?_ ?_
                          · rintro _ ⟨q', ⟨⟩⟩ mK hinvK; m6_nojoin; exact hJp (q', ()) mK hinvK
                          · intro Jq hJq
                            let d := hJq (q, ()) m1 ⟨hoq, by omega, wstk1, hlen1,
                              fun i hi => hout1 i (by omega), hpre1, hm1⟩
                            m6_to_jnz
                            refine wp_jnz_of (fun _ => ?_) (fun _ => by m6_nojoin; exact d)
                            m6_to_jnz
                            refine wp_jnz_of (fun hc_cr => ?_) (fun _ => by m6_nojoin; exact d)
                            have hkp : cr.toNat < keep_before.toNat := by
                              simp only [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc_cr
                              have h2 : ((wstk1[(p + 1#64).toNat]'hp1_w).setWidth 64).toNat <
                                  keep_before.toNat := hc_cr
                              rwa [zext_toNat _ (by decide), hcr_eq] at h2
                            have hq1_eq : (q + 1#64).toNat = q.toNat + 1 := bv64_add1 (by omega)
                            have hq2_eq : (q + 2#64).toNat = q.toNat + 2 := bv64_add2 (by omega)
                            have hq1_w : (q + 1#64).toNat < wstk1.length := by omega
                            m6_nojoin
                            let wstk2 := (wstk1.set q.toNat w0).set (q.toNat + 1) cr
                            have hm_eq : (wstk1.set q.toNat w0).set (q + 1#64).toNat
                                (wstk1[(p + 1#64).toNat]'hp1_w) = wstk2 := by
                              simp only [wstk2, hq1_eq, hcr_eq]
                            obtain ⟨hout', hpre'⟩ := sweep_bins_range_large_keep hoq hqp hq_w
                              (by simp [hlen1]; omega) hout1 hpre1 hlg hcr_lt hkp hcr_ref hq2_eq
                            exact hJq (q + 2#64, ()) _
                              ⟨by rw [hq2_eq]; omega, by rw [hq2_eq]; omega, wstk2,
                               by simp [wstk2, hlen1], hout', hpre', by rw [← hm_eq]; exact hm⟩
                        · exfalso; rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_np1
                          apply hc_np1
                          change (p + 1#64).toNat < (offW.setWidth 64 + szW.setWidth 64).toNat
                          rw [hp1_eq, BitVec.toNat_add, zext_toNat offW (by decide),
                            zext_toNat szW (by decide), hoff_eq, hsz_eq, hend_mod]
                          omega
                · have hp_end : p.toNat = end0 := by
                    have h1 := hc
                    simp only [h1bv, hmod0, hmod1,
                      hoff_idx, hsz_idx, hend_mod] at h1
                    omega
                  m6_c0_steps
                  refine wp_loop_inv
                    (fun (k, ()) m2 => q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                      ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                        (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                        (FullMem c (sweepBinState s wvecL wstk2 wuL nb1 ws1) ⋆ R) m2)
                    (fun (k, ()) _ => end0 - k.toNat) (fun J2 hLoop2 => ?_) ?_
                  · m6_c0_steps
                    exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1, fun _ _ => rfl,
                      hm1⟩
                  · rintro J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2
                    m6_split_fast
                    · have hk_lt : k.toNat < end0 := by
                        have h1 := hc
                        simp only [h1bv, hmod0, hmod1,
                          hoff_idx, hsz_idx, hend_mod] at h1
                        omega
                      have hk1_eq : (k + 1#64).toNat = k.toNat + 1 := bv64_add1 (by omega)
                      have hk_w : k.toNat < wstk2.length := by omega
                      m6_usteps; apply wp_store_sep
                      · exact FullArenaTactics.c0_store_full_wstk _ hk_w hm2
                      intro m hm; m6_nojoin
                      exact hLoop2 (k + 1#64, ()) _ (by dsimp only; rw [hk1_eq]; omega)
                        ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                         wstk2.set k.toNat 0xFFFFFFFF#32, by simp [hlen2],
                         fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
                    · obtain ⟨hqoff_bv, hlenF, hwatF, hltF⟩ := sweep_bins_range_exit_lit
                        (wstk1 := wstk1) hws1
                        (hlenL.with_scratch { hlenL.scratch_ok with wsort_len := hws1 })
                        hdkp hwatL hltL hl_lt hlen2 hoff_eq hsz_eq
                        h2l1_eq (by rw [hoff_eq]; exact hoq)
                        (by rw [hoff_eq, hsz_eq]; exact show q.toNat ≤ end0 from hp_end ▸ hqp)
                        (fun i hi => by
                          rw [hoff_eq, hsz_eq] at hi
                          have hi' : i < off0 ∨ p.toNat ≤ i := by rw [hp_end]; exact hi
                          exact hout1 i hi')
                        (fun i hi => by
                          rw [hoff_eq, hsz_eq] at hi
                          exact hout2 i (show i < q.toNat ∨ end0 ≤ i from hi))
                        (by rw [hoff_eq]; exact hpre1)
                      c0_hsteps
                      exact hLoopL (l + 1#64, ()) _ (by dsimp only; rw [hl1_eq]; omega)
                        ⟨by rw [hl1_eq]; omega, _, wstk2, _, nb1, ws1, hlenF, hwatF,
                         fun j hj => hltF j (hl1_eq ▸ hj), hm⟩
            · intro J hJ
              exact sweep_bins_lfix_wp J
                (@FullArenaTactics.c0_load_full_lvl c sL R mL (l >>> (1 : Nat)) hlv_lt hmL)
                (@FullArenaTactics.c0_load_full_vals c sL R mL l hl_v hmL)
                (fun _ => hJ _ _ rfl)
        · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
            have : ¬ (l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat) := by
              c0_bound
            omega
          rw [hl_eq] at hltL; clear hwvL_len hwsL_len hm0 hc
          m6_steps; c0_call hdefrag
          refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
            fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hslice' hm' => ?_⟩
          let s' : FullState :=
            { sL with
              core := { sL.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
              scratch := { sL.scratch with wsort := wsort' } }
          have hlt' : ∀ j < 2 * s.core.cur_vars, WatchSliceLtOk keep_before.toNat F_cur s'.core j
              (fullWatchOff s' j) (fullWatchSize s' j) := fun j hj => by
            obtain ⟨hsz_j, hws_j⟩ := hslice' j hj; rw [hsz_j]
            exact WatchSliceLtOk.relocate (k := sL.core) (k' := s'.core)
              (p := fullWatchOff sL j) (p' := fullWatchOff s' j)
              (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
              (fun _ hr _ => hr) (fun k hk => hws_j k hk) (hltL j hj)
          have hwat' : ModeWatchesInv F_cur s'.core := by
            unfold ModeWatchesInv; split
            · exact ⟨hlay', fun j hj => (hlt' j hj).toWatchSliceOk⟩
            · next hd =>
              by_cases hkz : keep_before.toNat = 0
              · exact ⟨hlay', fun j hj =>
                  (WatchSliceLtOk.toBinOnly (hkz ▸ hlt' j hj)).toDenseWatchSliceOk⟩
              · exfalso; exact hd (by simpa [s', sL] using hdkp (Nat.pos_of_ne_zero hkz))
          exact hQ wvec' wstk' wlen' nbL wsort' _ hlen' hlay' hlt'
            { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' } hm'

/-! ## 2. `full_sweep_bins_m6cf_wp` & `full_sweep_bins_wp` -/

private theorem m6cf_zero_off_preserves {c : FullCfg} {F_cur : List (List Nat)}
    {kL : FullCoreState} {sc : FullScratch} {l : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hwatL : ModeWatchesInv F_cur kL)
    (hbinL : ∀ j < l, BinOnlyWatchSliceOk F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hsz0 : fullWatchSizeCore kL l = 0) :
    let wvec' := kL.wvec.set (2 * l) 0#32
    let k' : FullCoreState := { kL with wvec := wvec' }
    FullState.LengthsOk c ⟨k', sc⟩ ∧ ModeWatchesInv F_cur k' ∧
    ∀ j < l + 1, BinOnlyWatchSliceOk F_cur k' j (fullWatchOffCore k' j)
      (fullWatchSizeCore k' j) := by
  intro wvec' k'
  have hcv := hlenL.cur_vars_le; have hwv := hlenL.wvec_len
  have h2l_lt : 2 * l < kL.wvec.length := by omega
  have hoff_l : fullWatchOffCore k' l = 0 := by
    unfold fullWatchOffCore k' wvec'; rw [List.getElem?_set_self h2l_lt, Option.getD_some]; rfl
  have hsz_l : fullWatchSizeCore k' l = 0 := by
    unfold fullWatchSizeCore k' wvec'; rw [List.getElem?_set_ne (by omega)]; exact hsz0
  have hne_eq : ∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j := fun j hj => by
    unfold fullWatchOffCore fullWatchSizeCore k' wvec'
    constructor <;> rw [List.getElem?_set_ne (by omega)]
  have hlay' : WatchStackLayout k' :=
    ⟨fun j hj => by
       by_cases hjl : j = l
       · subst hjl; rw [hoff_l, hsz_l]; exact Nat.zero_le _
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]; exact hwatL.layout.bounds j hj,
     fun j hj hp => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz_l] at hp; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hp
         exact hwatL.layout.pos_off j hj hp,
     fun j1 j2 h1 h2 hne hp1 hp2 => by
       by_cases hj1 : j1 = l
       · subst hj1; rw [hsz_l] at hp1; omega
       · by_cases hj2 : j2 = l
         · subst hj2; rw [hsz_l] at hp2; omega
         · obtain ⟨ho1, hs1⟩ := hne_eq j1 hj1; obtain ⟨ho2, hs2⟩ := hne_eq j2 hj2
           rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
           exact hwatL.layout.disjoint j1 j2 h1 h2 hne hp1 hp2,
     fun j hj idx hi => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz_l] at hi; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hi
         exact hwatL.layout.no_sentinel j hj idx hi⟩
  have hwat' : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv
    by_cases hdm : kL.dense_mode = 0#64
    · rw [rw_ite_pos hdm]
      have hwat0 : WatchesInv F_cur kL := by
        have h := hwatL; unfold ModeWatchesInv at h; rwa [rw_ite_pos hdm] at h
      refine ⟨hlay', fun j hj => ?_⟩
      by_cases hjl : j = l
      · subst hjl; rw [hsz_l]; exact .empty
      · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
        exact WatchSliceOk.mono (k := kL) (k' := k')
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl) (hwat0.slices j hj)
    · rw [rw_ite_neg hdm]
      have hwat0 : DenseWatchesInv F_cur kL := by
        have h := hwatL; unfold ModeWatchesInv at h; rwa [rw_ite_neg hdm] at h
      refine ⟨hlay', fun j hj => ?_⟩
      by_cases hjl : j = l
      · subst hjl; rw [hsz_l]; exact .empty
      · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
        exact DenseWatchSliceOk.mono (k := kL) (k' := k')
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl) (hwat0.slices j hj)
  refine ⟨⟨{ hlenL with wvec_len := by dsimp only [k', wvec']; rw [List.length_set, hwv] },
    hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst hjl; rw [hsz_l]; exact .empty
  · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
    exact BinOnlyWatchSliceOk.relocate (k := kL) (k' := k')
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) (fun _ _ => rfl)
      (hbinL j (by omega))

private theorem full_sweep_bins_finish_lit {c : FullCfg} {F_cur : List (List Nat)}
    {kL : FullCoreState} {sc : FullScratch} {wstk1 wstk2 : List (BitVec 32)}
    {wu' nb1 : BitVec 64} {l q_nat : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hwatL : ModeWatchesInv F_cur kL)
    (hbinL : ∀ j < l, BinOnlyWatchSliceOk F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hlen2 : wstk2.length = c.wcap)
    (hoq : fullWatchOffCore kL l ≤ q_nat)
    (hqe : q_nat ≤ fullWatchOffCore kL l + fullWatchSizeCore kL l)
    (hout1 : ∀ i, i < fullWatchOffCore kL l ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk1[i]? = kL.wstk[i]?)
    (hout2 : ∀ i, i < q_nat ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk2[i]? = wstk1[i]?)
    (hpre1 : BinOnlyWatchSliceOk F_cur { kL with wstk := wstk1 } l (fullWatchOffCore kL l)
      (q_nat - fullWatchOffCore kL l))
    (kL' : FullCoreState)
    (hk' : kL' = { kL with wvec := kL.wvec.set (2 * l + 1)
                                     (BitVec.ofNat 32 (q_nat - fullWatchOffCore kL l)),
                           wstk := wstk2, wusable := wu', num_binary := nb1 }) :
    FullState.LengthsOk c ⟨kL', sc⟩ ∧ ModeWatchesInv F_cur kL' ∧
    ∀ j < l + 1, BinOnlyWatchSliceOk F_cur kL' j (fullWatchOffCore kL' j)
      (fullWatchSizeCore kL' j) := by
  subst hk'
  let off0 := fullWatchOffCore kL l; let sz0 := fullWatchSizeCore kL l
  let wvec' := kL.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q_nat - off0))
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = kL.wstk[i]? :=
    fun i hi => by rw [hout2 i (by omega), hout1 i (by omega)]
  have hbin_l : BinOnlyWatchSliceOk F_cur { kL with wstk := wstk2 } l off0 (q_nat - off0) :=
    BinOnlyWatchSliceOk.relocate (k := { kL with wstk := wstk1 }) (k' := { kL with wstk := wstk2 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun j hj => hout2 (off0 + j) (Or.inl (by omega))) hpre1
  have hmode_l : ModeWatchSliceOk (decide (kL.dense_mode ≠ 0#64)) F_cur { kL with wstk := wstk2 }
      l off0 (q_nat - off0) := by
    by_cases hd : decide (kL.dense_mode ≠ 0#64) = true
    · simp only [ModeWatchSliceOk, hd, ↓reduceIte]; exact hbin_l.toDenseWatchSliceOk
    · simp only [ModeWatchSliceOk, hd, Bool.false_eq_true, ↓reduceIte]; exact hbin_l.toWatchSliceOk
  have hwat' := modeWatchesInv_shrink_slice hwatL hlenL hl_lt (new_sz := q_nat - off0) (by omega)
    hout_fin wu' nb1 hmode_l
  obtain ⟨_, hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hwatL.layout hlenL hl_lt
      (new_sz := q_nat - off0) (by omega) hout_fin hbin_l.ne_sentinel wu' nb1
  refine ⟨⟨{ hlenL with wvec_len := by simp [hlenL.wvec_len],
                        wstk_len_arr := hlen2 }, hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst j; rw [hoff_self, hsz_self]
    exact BinOnlyWatchSliceOk.relocate (k := { kL with wstk := wstk2 })
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p)
      (Nat.le_refl _) (fun _ _ => rfl) hbin_l
  · obtain ⟨ho, hs, hws⟩ := hother j (by omega) hjl; rw [ho, hs]
    exact BinOnlyWatchSliceOk.relocate (k := kL)
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) hws (hbinL j (by omega))

private theorem sweep_bins_m6cf_bin_keep {F_cur : List (List Nat)} {s : FullState}
    {l q : BitVec 64} {off0 p_nat : Nat} {wvecL wstk1 wstkL : List (BitVec 32)}
    {wuL nbL : BitVec 64} {w0 : BitVec 32}
    (hoq : off0 ≤ q.toNat) (hqp : q.toNat ≤ p_nat) (hq_w : q.toNat < wstk1.length)
    (hout1 : ∀ i, i < off0 ∨ p_nat ≤ i → wstk1[i]? = wstkL[i]?)
    (hpre1 : BinOnlyWatchSliceOk F_cur
      { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
      l.toNat off0 (q.toNat - off0))
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt_o : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hent_o : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [l.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hq1_eq : (q + 1#64).toNat = q.toNat + 1) :
    (∀ i, i < off0 ∨ p_nat + 1 ≤ i → (wstk1.set q.toNat w0)[i]? = wstkL[i]?) ∧
    BinOnlyWatchSliceOk F_cur
      { s.core with wvec := wvecL, wstk := wstk1.set q.toNat w0, wusable := wuL, num_binary := nbL }
      l.toNat off0 ((q + 1#64).toNat - off0) := by
  refine ⟨fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega), ?_⟩
  rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
  exact BinOnlyWatchSliceOk.append_bin
    (k := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL })
    (k' := { s.core with wvec := wvecL, wstk := wstk1.set q.toNat w0, wusable := wuL,
                         num_binary := nbL })
    (p := off0) (p' := off0) (Nat.le_refl _) (fun _ _ => List.getElem?_set_ne (by omega)) hpre1
    (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]; exact List.getElem?_set_self hq_w)
    hbin hne hlt_o hent_o

private theorem sweep_bins_m6cf_exit_lit {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {l q : BitVec 64} {offW szW : BitVec 32} {wvecL wstkL wstk1 wstk2 : List (BitVec 32)}
    {wuL nbL nb1 : BitVec 64} {wsort1 : List (BitVec 32)} (_hws1 : wsort1.length = 2 * c.max_vars)
    (hlenL : FullState.LengthsOk c
      { core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL }
        scratch := { s.scratch with wsort := wsort1 } })
    (hwatL : ModeWatchesInv F_cur
      { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL })
    (hbinL : ∀ j < l.toNat, BinOnlyWatchSliceOk F_cur
      { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL } j
      (fullWatchOffCore
        { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL } j)
      (fullWatchSizeCore
        { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL } j))
    (hl_lt : l.toNat < 2 * s.core.cur_vars) (hlen2 : wstk2.length = c.wcap)
    (hoff_eq : offW.toNat = fullWatchOffCore
      { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL } l.toNat)
    (hsz_eq : szW.toNat = fullWatchSizeCore
      { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL } l.toNat)
    (h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1)
    (hoq : offW.toNat ≤ q.toNat) (hqp : q.toNat ≤ offW.toNat + szW.toNat)
    (hout1 : ∀ i, i < offW.toNat ∨ offW.toNat + szW.toNat ≤ i → wstk1[i]? = wstkL[i]?)
    (hout2 : ∀ i, i < q.toNat ∨ offW.toNat + szW.toNat ≤ i → wstk2[i]? = wstk1[i]?)
    (hpre1 : BinOnlyWatchSliceOk F_cur
      { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
      l.toNat offW.toNat (q.toNat - offW.toNat)) :
    let qbv := (q - offW.setWidth 64).setWidth 32
    let wvec1 := wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat qbv
    let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
    let k1 : FullCoreState := (sweepBinState s wvec1 wstk2 wu' nb1 wsort1).core
    qbv = BitVec.ofNat 32 (q.toNat - offW.toNat) ∧
    FullState.LengthsOk c ⟨k1, { s.scratch with wsort := wsort1 }⟩ ∧
    ModeWatchesInv F_cur k1 ∧
    ∀ j < l.toNat + 1, BinOnlyWatchSliceOk F_cur k1 j (fullWatchOffCore k1 j)
      (fullWatchSizeCore k1 j) := by
  intro qbv wvec1 wu' k1
  have hlt32 : q.toNat - offW.toNat < 2 ^ 32 := by omega
  have hqbv : qbv = BitVec.ofNat 32 (q.toNat - offW.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    have : (2 ^ 64 - offW.toNat + q.toNat) % 2 ^ 64 = q.toNat - offW.toNat := by omega
    rw [this, Nat.mod_eq_of_lt hlt32]
  have hwvec_eq : wvec1 = wvecL.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - offW.toNat)) := by
    dsimp only [wvec1]; rw [h2l1_eq, hqbv]
  let kL : FullCoreState :=
    { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL }
  have hfin := full_sweep_bins_finish_lit (kL := kL)
    hlenL.core_ok hlenL.scratch_ok hwatL hbinL hl_lt hlen2 (hoff_eq ▸ hoq)
    (hoff_eq ▸ hsz_eq ▸ hqp) (fun i hi => hout1 i (by rw [hoff_eq, hsz_eq]; exact hi))
    (fun i hi => hout2 i (by rw [hoff_eq, hsz_eq]; exact hi)) (hoff_eq ▸ hpre1) k1
    (by dsimp only [k1, kL]; rw [hwvec_eq, hoff_eq])
  exact ⟨hqbv, hfin.1, hfin.2.1, hfin.2.2⟩

theorem full_sweep_bins_m6cf_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Func.wp Γ full_sweep_bins_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le; have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len; have hl_len := hlen.core_ok.lvl_len
  have hws_len := hlen.scratch_ok.wsort_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [bv64_shl1_nat_eq (by rw [bv64_ofNat_toNat_id (by omega)]; omega),
      bv64_ofNat_toNat_id (by omega)]
  unfold Func.wp full_sweep_bins_m6cf_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (si, ()) m0 => si.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wsort0 : List (BitVec 32), wsort0.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with wsort := wsort0 } } ⋆ R) m0)
    (fun (si, ()) _ => 2 * s.core.cur_vars - si.toNat)
    (fun J0 hLoop0 => by c0_hsteps; exact hLoop0 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort,
      hws_len, hm⟩)
    (fun J0 ⟨si, ⟨⟩⟩ m0 ⟨hsi_le, wsort0, hws0_len, hm0⟩ hLoop0 => ?_)
  c0_hsplit
  · have hsi_lt : si.toNat < 2 * s.core.cur_vars := by
      have : si.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      omega
    have hsi1_eq : (si + 1#64).toNat = si.toNat + 1 := bv64_add1 (by omega)
    have hsi_ws : si.toNat < wsort0.length := by omega
    c0_hsteps
    exact hLoop0 (si + 1#64, ()) _ (by dsimp only; rw [hsi1_eq]; omega)
      ⟨by rw [hsi1_eq]; omega, wsort0.set si.toNat 0xFFFFFFFF#32, by simp [hws0_len], hm⟩
  · clear hLoop0 J0
    have hlen0 : ({ s with scratch := { s.scratch with wsort := wsort0 } } : FullState).LengthsOk
        c := hlen.with_scratch { hlen.scratch_ok with wsort_len := hws0_len }
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (l, ()) mL => l.toNat ≤ 2 * s.core.cur_vars ∧
        ∃ wvecL wstkL wuL nbL wsortL,
          let sL := sweepBinState s wvecL wstkL wuL nbL wsortL
          sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
          (∀ j < l.toNat, BinOnlyWatchSliceOk F_cur sL.core j (fullWatchOff sL j)
            (fullWatchSize sL j)) ∧ (FullMem c sL ⋆ R) mL)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun JL hLoopL => by c0_hsteps; exact hLoopL (0#64, ()) m0 ⟨Nat.zero_le _, s.core.wvec,
        s.core.wstk, s.core.wusable, s.core.num_binary, wsort0, hlen0, hw.watches,
        fun _ hj => absurd hj (Nat.not_lt_zero _), hm0⟩)
      (fun JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, wsortL, hlenL, hwatL, hbinL, hmL⟩
          hLoopL => ?_)
    let sL := sweepBinState s wvecL wstkL wuL nbL wsortL
    have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
    have hwsL_len : wsortL.length = 2 * c.max_vars := hlenL.scratch_ok.wsort_len
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      obtain ⟨h2l_lt, h2l1_lt, hl1_eq, hmod0, hmod1, hbd_end, hslice0⟩ :=
        full_sweep_bins_lit_hdr_facts hlenL.core_ok hwatL hcv_le hmax_lt hl_lt
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_nat_eq (by omega)
      have hl1_eq' : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := hl1_eq
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [BitVec.toNat_add, h2l_eq, show (1 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have h1bv : (1 : BitVec 64).toNat = 1 := rfl
      let off0 : Nat := fullWatchOff sL l.toNat; let sz0 : Nat := fullWatchSize sL l.toNat
      let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
      let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by omega)
      have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOff fullWatchOffCore sL sweepBinState
        rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSize fullWatchSizeCore sL sweepBinState
        rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
      have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
      clear hw hlen hdefrag hQ hlen0 hm0
      c0_hsplit
      · have hsz0 : sz0 = 0 := by
          have h1 := congrArg BitVec.toNat hc; simp only [h1bv, hmod1] at h1
          rw [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
          simpa using h1
        have h2l_w : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; exact h2l_lt
        c0_hsteps
        obtain ⟨hlenZ, hwatZ, hbinZ⟩ :=
          m6cf_zero_off_preserves hlenL.core_ok hlenL.scratch_ok hwatL hbinL hl_lt hsz0
        let wvecZ := wvecL.set (2 * l.toNat) 0#32
        have hwvZ_eq : wvecL.set (l <<< (1 : Nat)).toNat 0 = wvecZ := by
          dsimp only [wvecZ]; rw [h2l_eq]; rfl
        exact hLoopL (l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq']; omega)
          ⟨by rw [hl1_eq']; omega, wvecZ, wstkL, wuL, nbL, wsortL, hlenZ, hwatZ,
           hl1_eq' ▸ hbinZ, full_mem_eq_cast hm (by dsimp only [sL]; rw [hwvZ_eq])⟩
      · have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
        have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
        have hl_v : l.toNat < s.core.vals.length := by omega
        let end0 : Nat := off0 + sz0
        have hend_le : end0 ≤ c.wcap :=
          le_trans hbd_end hlenL.core_ok.wlen_le
        have hend_mod : (off0 + sz0) % 2 ^ 64 = off0 + sz0 :=
          Nat.mod_eq_of_lt (by omega)
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
          ?_ ?_
        · intro _ _ _; c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
            (fun _ => True) ?_ ?_
          · intro _ _ _; c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (p, q, ()) m1 =>
                off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
                ∃ wstk1 nb1 wsort1, wstk1.length = c.wcap ∧ wsort1.length = 2 * c.max_vars ∧
                  (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
                  ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat (end0 - p.toNat) ∧
                  BinOnlyWatchSliceOk F_cur
                    { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
                    l.toNat off0 (q.toNat - off0) ∧
                  (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 wsort1) ⋆ R) m1)
              (fun (p, _, ()) _ => end0 - p.toNat)
              (fun J1 hLoop1 => by
                c0_hsteps
                have hoff64 : (offW.setWidth 64).toNat = off0 := by
                  rw [zext_toNat offW (by decide), hoff_eq]
                exact hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
                  by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
                  wstkL, nbL, wsortL, hlenL.core_ok.wstk_len_arr, hwsL_len, fun _ _ => rfl,
                  by rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0,
                  by rw [hoff64, Nat.sub_self]; exact .empty, hmL⟩)
              (fun J1 ⟨p, q, ⟨⟩⟩ m1
                  ⟨hoq, hqp, hpe, wstk1, nb1, wsort1, hlen1, hws1, hout1, hrem1, hpre1, hm1⟩
                  hLoop1 => ?_)
            have hend_bv : (offW.setWidth 64 + szW.setWidth 64).toNat = end0 := by
              rw [BitVec.toNat_add, zext_toNat offW (by decide), zext_toNat szW (by decide),
                hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega)]
            c0_hsplit
            · have hp_lt : p.toNat < end0 := by
                simp only [h1bv, hmod0, hmod1,
                  hoff_idx, hsz_idx, hend_mod] at hc
                omega
              have hp_w : p.toNat < wstk1.length := by omega
              have hq_w : q.toNat < wstk1.length := by omega
              let w0 := wstk1[p.toNat]'hp_w
              have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
                dsimp only [sL, sweepBinState]
                rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
              have hstep := hrem1.step (by omega) hw0_orig
              c0_hsteps_nogrp; c0_hstep; c0_hsplit
              · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
                obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
                have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
                have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := bv64_add1 (by omega)
                have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
                have hot_sh : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat =
                    (w0 &&& 0x7FFFFFFF#32).toNat / 2 := bv32_shr1_toNat _
                have hot_lvl : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
                    s.core.lvl.length := by rw [zext_toNat _ (by decide), hot_sh]; omega
                have hot_v : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
                  rw [zext_toNat _ (by decide)]; omega
                have hot_ws : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < wsort1.length := by
                  rw [zext_toNat _ (by decide)]; omega
                c0_hsteps_nogrp
                refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                  (fun _ => True) ?_ ?_
                · intro _ _ _; c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                    (fun _ => True) ?_ ?_
                  · intro _ _ _; c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                      (fun _ => True) ?_ ?_
                    · intro _ _ _; c0_hsteps_nogrp
                      refine wp_join_group (fun (q', ()) mQ =>
                        off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 1 ∧
                        ∃ wstk' nb' wsort', wstk'.length = c.wcap ∧
                          wsort'.length = 2 * c.max_vars ∧
                          (∀ i, i < off0 ∨ p.toNat + 1 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                          BinOnlyWatchSliceOk F_cur
                            (sweepBinState s wvecL wstk' wuL nbL wsort').core
                            l.toNat off0 (q'.toNat - off0) ∧
                          (FullMem c (sweepBinState s wvecL wstk' wuL nb' wsort') ⋆ R) mQ) ?_ ?_
                      · rintro _ ⟨q', ⟨⟩⟩ mQ ⟨hoq', hqp', wstk', nb', wsort', hlen', hws', hout',
                          hpre', hmQ⟩
                        c0_hsteps
                        exact hLoop1 (p + (1 : BitVec 64), q', ()) mQ
                          (by dsimp only; rw [hp1_eq]; omega)
                          ⟨hoq', by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, wstk', nb', wsort',
                           hlen', hws', by rw [hp1_eq]; exact hout',
                           by rw [hp1_eq, show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                              exact hrem', hpre', hmQ⟩
                      · intro Jq hJq; c0_hsplit
                        · c0_hsteps
                          · exact hJq (q, ()) _ ⟨hoq, by omega, wstk1, nb1 - 1#64, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm⟩
                          · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm1⟩
                          · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm1⟩
                        · c0_hsteps_nogrp
                          refine wp_join_state0 (α := List (BitVec 32))
                            (fun wsort' mS => wsort'.length = 2 * c.max_vars ∧
                              (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 wsort') ⋆ R) mS)
                            ?_ ?_
                          · rintro _ wsort' mS ⟨hws', hmS⟩; c0_hsteps
                            obtain ⟨hout', hpre'⟩ := sweep_bins_m6cf_bin_keep hoq hqp hq_w hout1
                              hpre1 hbin hne hlt_o hent_o hq1_eq
                            exact hJq (q + (1 : BitVec 64), ()) _
                              ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                               wstk1.set q.toNat w0, nb1, wsort', List.length_set.trans hlen1,
                               hws', hout', hpre', hm⟩
                          · intro Js hJs; c0_hsplit
                            · c0_hsteps; exact hJs _ _ ⟨by simp [hws1], hm⟩
                            · c0_hsteps; exact hJs wsort1 m1 ⟨hws1, hm1⟩
                    · intro Jd hJd; clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1
                        hout1 hstep
                      c0_hsplit
                      · c0_hsteps; exact hJd _ trivial
                      · c0_hsplit
                        · c0_hsteps; exact hJd _ trivial
                        · c0_hsplit
                          · c0_hsteps; exact hJd _ trivial
                          · c0_hsplit <;> (c0_hsteps <;> exact hJd _ trivial)
                  · intro Jo hJo; clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1
                      hout1 hstep
                    c0_hsplit
                    · c0_hsteps; exact hJo _ trivial
                    · c0_hsplit
                      · c0_hsplit <;> (c0_hsplit <;> (c0_hsteps <;> exact hJo _ trivial))
                      · c0_hsteps; exact hJo _ trivial
                · intro Jos hJos; clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1
                    hout1 hstep
                  c0_hsplit <;> (try c0_hsplit) <;> (c0_hsteps <;> exact hJos _ trivial)
              · have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
                obtain ⟨h2rem, _, _, _, _, _, hrem'⟩ := hstep.2 hlg
                have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
                c0_hsteps
                exact hLoop1 (p + (2 : BitVec 64), q, ()) m1 (by dsimp only; rw [hp2_eq]; omega)
                  ⟨hoq, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, wstk1, nb1, wsort1, hlen1,
                   hws1, fun i hi => by rw [hp2_eq] at hi; exact hout1 i (by omega),
                   by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                      exact hrem', hpre1, hm1⟩
            · have hp_end : p.toNat = end0 := by
                simp only [h1bv, hmod0, hmod1,
                  hoff_idx, hsz_idx, hend_mod] at hc
                omega
              clear hrem1 hslice0 hLoop1 J1; c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (k, ()) m2 => q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                  ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                    (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                    (FullMem c (sweepBinState s wvecL wstk2 wuL nb1 wsort1) ⋆ R) m2)
                (fun (k, ()) _ => end0 - k.toNat)
                (fun J2 hLoop2 => ?_)
                (fun J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2 => ?_)
              · c0_hsteps; exact hLoop2 (q, ()) m1
                  ⟨Nat.le_refl _, by omega, wstk1, hlen1, fun _ _ => rfl, hm1⟩
              c0_hsplit
              · have hk_lt : k.toNat < end0 := by
                  simp only [h1bv, hmod0, hmod1,
                    hoff_idx, hsz_idx, hend_mod] at hc
                  omega
                have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1 (by omega)
                c0_hsteps
                exact hLoop2 (k + (1 : BitVec 64), ()) _ (by dsimp only; rw [hk1_eq]; omega)
                  ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                   wstk2.set k.toNat 0xFFFFFFFF#32, List.length_set.trans hlen2,
                   fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
              · clear hLoop2 J2
                let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
                c0_hsteps_nogrp
                refine wp_join_state0 (α := List (BitVec 32))
                  (fun wvec' mW =>
                    let kF : FullCoreState :=
                      { s.core with
                        wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 }
                    FullState.LengthsOk c ⟨kF, { s.scratch with wsort := wsort1 }⟩ ∧
                    ModeWatchesInv F_cur kF ∧
                    (∀ j < l.toNat + 1,
                      BinOnlyWatchSliceOk F_cur kF j (fullWatchOffCore kF j)
                        (fullWatchSizeCore kF j)) ∧
                    (FullMem c (sweepBinState s wvec' wstk2 wuL nb1 wsort1) ⋆ R) mW) ?_ ?_
                · rintro _ wvec' mW ⟨hlenF, hwatF, hbinF, hmW⟩; c0_hsteps
                  exact hLoopL (l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq']; omega)
                    ⟨by rw [hl1_eq']; omega, wvec', wstk2, wu', nb1, wsort1, hlenF, hwatF,
                     hl1_eq' ▸ hbinF, full_mem_eq_cast hm rfl⟩
                · intro Jw hJw
                  obtain ⟨hqbv, hlen1', hwat1', hbin1'⟩ := sweep_bins_m6cf_exit_lit
                    (wstk1 := wstk1) hws1
                    (hlenL.with_scratch { hlenL.scratch_ok with wsort_len := hws1 }) hwatL hbinL
                    hl_lt hlen2 hoff_eq hsz_eq h2l1_eq (by rw [hoff_eq]; exact hoq)
                    (by rw [hoff_eq, hsz_eq]; exact show q.toNat ≤ end0 from hp_end ▸ hqp)
                    (fun i hi => by
                      rw [hoff_eq, hsz_eq] at hi
                      have hi' : i < off0 ∨ p.toNat ≤ i := by rw [hp_end]; exact hi
                      exact hout1 i hi')
                    (fun i hi => by
                      rw [hoff_eq, hsz_eq] at hi
                      exact hout2 i (show i < q.toNat ∨ end0 ≤ i from hi))
                    (by rw [hoff_eq]; exact hpre1)
                  let wvec1 := wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                    ((q - offW.setWidth 64).setWidth 32)
                  c0_hsplit
                  · have hq_eq : q.toNat = off0 := by
                      have h1 := congrArg BitVec.toNat hc; simp only [hmod0] at h1
                      rwa [zext_toNat _ (by decide), hoff_idx] at h1
                    have hsz1_zero : fullWatchSizeCore
                        { s.core with wvec := wvec1, wstk := wstk2, wusable := wu',
                                      num_binary := nb1 } l.toNat = 0 := by
                      unfold fullWatchSizeCore; dsimp only [wvec1]
                      rw [h2l1_eq, hqbv, hoff_eq, List.getElem?_set_self h2l1_lt, Option.getD_some,
                        hq_eq, Nat.sub_self]; rfl
                    obtain ⟨hlenZ, hwatZ, hbinZ⟩ := m6cf_zero_off_preserves hlen1'.core_ok
                      hlen1'.scratch_ok hwat1' (fun j hj => hbin1' j (by omega)) hl_lt hsz1_zero
                    have h2l_w : (l <<< (1 : Nat)).toNat < wvecL.length := by
                      rw [h2l_eq]; exact h2l_lt
                    have h2l1_w : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
                        (wvecL.set (l <<< (1 : Nat)).toNat 0#32).length := by
                      rw [List.length_set, h2l1_eq]; exact h2l1_lt
                    c0_hsteps
                    have hwv_comm :
                        (wvecL.set (l <<< (1 : Nat)).toNat 0).set
                          ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat 0 =
                        wvec1.set (2 * l.toNat) 0#32 := by
                      dsimp only [wvec1]; rw [h2l_eq, h2l1_eq, hqbv, hoff_eq, hq_eq, Nat.sub_self]
                      exact List.set_comm (0 : BitVec 32) (0 : BitVec 32) (by omega)
                    exact hJw (wvec1.set (2 * l.toNat) 0#32) _
                      ⟨hlenZ, hwatZ, hbinZ, full_mem_eq_cast hm (by dsimp only; rw [hwv_comm])⟩
                  · have h2l1_w : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
                      rw [h2l1_eq]; exact h2l1_lt
                    c0_hsteps; exact hJw wvec1 _ ⟨hlen1', hwat1', hbin1', hm⟩
          · intro Jf hJf; clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
            c0_hsteps <;> exact hJf _ trivial
        · intro Js hJs; clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
          c0_hsteps <;> exact hJs _ trivial
    · have hl_end : l.toNat = 2 * s.core.cur_vars := by
        have : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤ l.toNat := by c0_bound
        omega
      have hbin_all : BinOnlyWatchesInv F_cur sL.core :=
        ⟨hwatL.layout, fun j hj => hbinL j (hl_end ▸ hj)⟩
      c0_hsteps; c0_call hdefrag
      refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
        fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hpres hm' => ?_⟩
      let sF : FullState :=
        { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                                num_binary := nbL }
          scratch := { s.scratch with wsort := wsort' } }
      have hbinF : BinOnlyWatchesInv F_cur sF.core :=
        fullWstackDefrag_preserves_binOnly hbin_all hlay' rfl hpres
      c0_hsteps
      exact hQ wvec' wstk' wlen' nbL wsort' m' hlen' hbinF.toFull hbinF.toDenseWatchesInv
        { hw with
          arena := { hw.arena with len_ok := hw.arena.len_ok }
          watches := hbinF.toModeWatchesInv }
        hm'

theorem full_sweep_bins_wp (Γ : Env)
    (hSub : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins_m6cf" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_sweep_bins_body
  c0_hsteps; c0_call hSub; rwa [collect_fwd0_sb]

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
