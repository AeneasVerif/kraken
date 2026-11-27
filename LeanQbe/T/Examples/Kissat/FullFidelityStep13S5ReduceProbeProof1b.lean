/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof1b0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_sort_reds` Proof (`FullFidelityStep13S5ReduceProbeProof1b`)

Proves `full_sort_reds_s5_wp` against `step13SortRedsSpec` (`Proof1b0`).
-/

set_option autoImplicit false

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open FullArenaTactics
open scoped FullArenaTactics FullReduceTactics

private abbrev insOuterInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (i : BitVec 64) (m1 : Mem 64) : Prop :=
  i.toNat ≤ n ∧ ∃ rr1 : List (BitVec 32), rr1.length = c.red_cap ∧
    (∀ k < n, ∃ j < n, rr1[k]? = s.scratch.red_refs[j]?) ∧
    (FullMem c { s with scratch := { s.scratch with red_refs := rr1 } } ⋆ R) m1

private abbrev insInnerInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n ub : Nat)
    (j : BitVec 64) (m2 : Mem 64) : Prop :=
  j.toNat ≤ ub ∧ ∃ rr2 : List (BitVec 32), rr2.length = c.red_cap ∧
    (∀ k < n, k ≠ j.toNat → ∃ j0 < n, rr2[k]? = s.scratch.red_refs[j0]?) ∧
    (FullMem c { s with scratch := { s.scratch with red_refs := rr2 } } ⋆ R) m2

private abbrev radixOuterInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (src dst shift : BitVec 64) (m1 : Mem 64) : Prop :=
  shift.toNat ≤ 64 ∧ shift.toNat % 8 = 0 ∧
  ∃ (use0 : Bool) (sb1 : List (BitVec 32)), sb1.length = c.scratch_cap ∧
    src = c.pScratchBuf + BitVec.ofNat 64 (4 * radixSrcOff use0 n) ∧
    dst = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0 n) ∧
    (∀ k < n, (sb1[radixSrcOff use0 n + k]?.getD 0#32).toNat < n) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb1 } } ⋆ R) m1

private abbrev radixPassPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (src dst : BitVec 64) (m2 : Mem 64) : Prop :=
  ∃ (use0' : Bool) (sb2 : List (BitVec 32)), sb2.length = c.scratch_cap ∧
    src = c.pScratchBuf + BitVec.ofNat 64 (4 * radixSrcOff use0' n) ∧
    dst = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0' n) ∧
    (∀ k < n, (sb2[radixSrcOff use0' n + k]?.getD 0#32).toNat < n) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb2 } } ⋆ R) m2

private abbrev radixZeroInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (sb1 : List (BitVec 32)) (b : BitVec 64) (m2 : Mem 64) : Prop :=
  b.toNat ≤ 256 ∧ ∃ sb2 : List (BitVec 32), sb2.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb2[j]? = sb1[j]?) ∧
    (∀ k < b.toNat, pairU64At sb2 (2 * n + k) = 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb2 } } ⋆ R) m2

private abbrev radixCountInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (sb1 : List (BitVec 32)) (keyFn : Nat → Nat) (i : BitVec 64) (m3 : Mem 64) : Prop :=
  i.toNat ≤ n ∧ ∃ sb3 : List (BitVec 32), sb3.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb3[j]? = sb1[j]?) ∧
    (∀ k < 256, (pairU64At sb3 (2 * n + k)).toNat = countPrefix keyFn i.toNat k) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb3 } } ⋆ R) m3

private abbrev radixPrefInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (sb1 : List (BitVec 32)) (keyFn : Nat → Nat) (bp pos : BitVec 64) (m4 : Mem 64) : Prop :=
  bp.toNat ≤ 256 ∧ pos.toNat = sumBuckets keyFn n bp.toNat ∧
  ∃ sb4 : List (BitVec 32), sb4.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb4[j]? = sb1[j]?) ∧
    (∀ k < bp.toNat, (pairU64At sb4 (2 * n + k)).toNat = sumBuckets keyFn n k) ∧
    (∀ k, bp.toNat ≤ k → k < 256 →
      (pairU64At sb4 (2 * n + k)).toNat = countPrefix keyFn n k) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb4 } } ⋆ R) m4

private abbrev radixScatterInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (use0 : Bool) (n : Nat) (sb1 : List (BitVec 32)) (keyFn : Nat → Nat)
    (is_ : BitVec 64) (m5 : Mem 64) : Prop :=
  is_.toNat ≤ n ∧ ∃ sb5 : List (BitVec 32), sb5.length = c.scratch_cap ∧
    (∀ j, j < 2 * n → sb5[j]? = sb1[j]?) ∧
    (∀ k < n, sb5[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?) ∧
    (∀ b < 256, (pairU64At sb5 (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn is_.toNat b) ∧
    (∀ b < 256, ∀ p, sumBuckets keyFn n b ≤ p →
      p < sumBuckets keyFn n b + countPrefix keyFn is_.toNat b →
      (sb5[radixDstOff use0 n + p]?.getD 0#32).toNat < n) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb5 } } ⋆ R) m5

private abbrev radixCopy1Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (use0 : Bool) (n : Nat) (ic1 : BitVec 64) (m2 : Mem 64) : Prop :=
  ic1.toNat ≤ n ∧ ∃ sb2 : List (BitVec 32), sb2.length = c.scratch_cap ∧
    (∀ k < n, (sb2[radixSrcOff use0 n + k]?.getD 0#32).toNat < n) ∧
    (∀ k < ic1.toNat, ∃ j < n, sb2[radixDstOff use0 n + k]? = s.scratch.red_refs[j]?) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb2 } } ⋆ R) m2

private abbrev radixCopy2Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (n : Nat)
    (sb2 : List (BitVec 32)) (ic2 : BitVec 64) (m3 : Mem 64) : Prop :=
  ic2.toNat ≤ n ∧ ∃ rr1 : List (BitVec 32), rr1.length = c.red_cap ∧
    (∀ k < ic2.toNat, ∃ j < n, rr1[k]? = s.scratch.red_refs[j]?) ∧
    (FullMem c { s with scratch := { s.scratch with red_refs := rr1, scratch_buf := sb2 } } ⋆ R)
      m3

private theorem sort_reds_radix_copy_tail {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} {use0 : Bool}
    {n src idx0P idx1P : BitVec 64} {sb1 : List (BitVec 32)} {m1 : Mem 64}
    (hrr_len : s.scratch.red_refs.length = c.red_cap)
    (hn_cap : n.toNat ≤ c.red_cap) (hcap : 4 * n.toNat + 512 ≤ c.scratch_cap)
    (hred_lt : c.red_cap < 2 * 2 ^ 28) (hn_pos : 0 < n.toNat) (hlen1 : sb1.length = c.scratch_cap)
    (hidx0 : idx0P = c.pScratchBuf + BitVec.ofNat 64 (4 * (2 * n.toNat)))
    (hidx1 : idx1P = c.pScratchBuf + BitVec.ofNat 64 (4 * (3 * n.toNat)))
    (hsrc_eq : src = c.pScratchBuf + BitVec.ofNat 64 (4 * radixSrcOff use0 n.toNat))
    (hsrc_lt : ∀ k < n.toNat, (sb1[radixSrcOff use0 n.toNat + k]?.getD 0#32).toNat < n.toNat)
    (hm1 : (FullMem c { s with scratch := { s.scratch with scratch_buf := sb1 } } ⋆ R) m1)
    (hQ : ∀ (rr' sb' : List (BitVec 32)) (m' : Mem 64),
      rr'.length = c.red_cap → sb'.length = c.scratch_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := sb' } } ⋆ R)
        m' →
      Q () m') :
    wp Γ Q X (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p_24 =>
      Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p_25 =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_25.fst, Arg.var n, ()))
          fun p_26 =>
        Expr.jnz (Arg.var p_26.fst)
          (Expr.let_ (Op.mk (.mul i64) (Arg.var p_25.fst, Arg.imm 4, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_24.fst, Arg.var p.fst, ())) fun p =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var p_25.fst, Arg.imm 4, ())) fun p_27 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var src, Arg.var p_27.fst, ())) fun p_28 =>
            Expr.load i32 (Arg.var p_28.fst) fun ld_6 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_6, ())) fun p_29 =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var p_29.fst, Arg.imm 4, ())) fun p_30 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_30.fst, ())) fun p_31 =>
            Expr.load i32 (Arg.var p_31.fst) fun ld =>
            Expr.store (t := i32) (Arg.var ld) (Arg.var p.fst)
              (Expr.let_ (Op.mk (.add i64) (Arg.var p_25.fst, Arg.imm 1, ())) fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ())))
          (Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p_27 =>
            Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_27.fst, Arg.var n, ()))
              fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var p_27.fst, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p.fst, ())) fun p =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p_27.fst, Arg.imm 4, ())) fun p_28 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p_24.fst, Arg.var p_28.fst, ())) fun p_29 =>
                Expr.load i32 (Arg.var p_29.fst) fun ld =>
                Expr.store (t := i32) (Arg.var ld) (Arg.var p.fst)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var p_27.fst, Arg.imm 1, ())) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ())))
              (Expr.ret ())) Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ())) Blocks.nil)
      fun Js =>
      Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var src, Arg.var idx0P, ())) fun p =>
      Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var idx1P, ()))
        (Expr.jump Js.fst (Arg.var idx0P, ()))) m1 := by
  let tmpOff := radixDstOff use0 n.toNat
  refine wp_join_group (ts := [i64])
    (fun (tmprr, ()) mt => mt = m1 ∧
      tmprr = c.pScratchBuf + BitVec.ofNat 64 (4 * tmpOff))
    (fun _ (tmprr, ()) mt ⟨hmt, htmpeq⟩ => by
      subst mt
      refine wp_loop_inv
        (fun (ic1, ()) m2 => radixCopy1Inv c s R use0 n.toNat ic1 m2)
        (fun (ic1, ()) _ => n.toNat - ic1.toNat)
        (fun Lc1 hLc1 => hLc1 (0#64, ()) m1 ⟨Nat.zero_le _, sb1, hlen1,
          hsrc_lt, (fun _ h => by cases h), hm1⟩)
        (fun Lc1 (ic1, ()) m2 ⟨hic1_le, sb2, hlen2, hsr2, hcp2, hm2⟩ hLc1 => by
          c0_hfast
          · have hic1_lt : ic1.toNat < n.toNat := by c0_bound
            obtain ⟨hld1, hld2, hok, hln', hsr', hcp', hst⟩ :=
              radix_copy1_step
                (s := { s with scratch := { s.scratch with scratch_buf := sb2 } })
                rfl rfl hlen2 hrr_len hcap hn_cap (by omega) hic1_lt hsrc_eq htmpeq hsr2 hcp2 hm2
            have hic1_n := bv64_succ_toNat ic1 (by omega)
            exact ⟨_, hld1, by decide, _, hld2, hok, hLc1 (ic1 + 1#64, ()) _
              (by dsimp only; rw [hic1_n]; omega)
              ⟨by rw [hic1_n]; omega, _, hln', hsr',
                by rw [hic1_n]; exact hcp', hst⟩⟩
          · have hcp2' : ∀ k < n.toNat, ∃ j < n.toNat,
                sb2[radixDstOff use0 n.toNat + k]? = s.scratch.red_refs[j]? :=
              fun k hk => hcp2 k (by omega)
            refine wp_loop_inv
              (fun (ic2, ()) m3 => radixCopy2Inv c s R n.toNat sb2 ic2 m3)
              (fun (ic2, ()) _ => n.toNat - ic2.toNat)
              (fun Lc2 hLc2 => hLc2 (0#64, ()) m2 ⟨Nat.zero_le _,
                s.scratch.red_refs, hrr_len, (fun _ h => by cases h), hm2⟩)
              (fun Lc2 (ic2, ()) m3 ⟨hic2_le, rr1, hlenr1, hcpr1, hm3⟩ hLc2 => by
                c0_hfast
                · have hic2_lt : ic2.toNat < n.toNat := by c0_bound
                  obtain ⟨hld, hok, hlnr', hcpr', hst⟩ :=
                    radix_copy2_step
                      (s := { s with scratch :=
                        { s.scratch with red_refs := rr1, scratch_buf := sb2 } })
                      rfl rfl hlen2 hlenr1 hcap hn_cap (by omega) hic2_lt htmpeq hcp2' hcpr1 hm3
                  have hic2_n := bv64_succ_toNat ic2 (by omega)
                  exact ⟨_, hld, hok, hLc2 (ic2 + 1#64, ()) _
                    (by dsimp only; rw [hic2_n]; omega)
                    ⟨by rw [hic2_n]; omega, _, hlnr',
                      by rw [hic2_n]; exact hcpr', hst⟩⟩
                · exact hQ rr1 sb2 m3 hlenr1 hlen2 (fun k hk => hcpr1 k (by omega)) hm3)))
    (fun Jtmp hJtmp => by
      c0_hfast
      · cases use0
        · exfalso; rw [hsrc_eq, hidx0] at hc
          have h4n := congrArg (fun x => (x - c.pScratchBuf).toNat) hc
          rw [BitVec.add_comm c.pScratchBuf, BitVec.add_sub_cancel,
            BitVec.add_comm c.pScratchBuf (BitVec.ofNat 64 (4 * (2 * n.toNat))),
            BitVec.add_sub_cancel] at h4n
          have h12n : 4 * radixSrcOff false n.toNat < 2 ^ 64 := by simp [radixSrcOff]; omega
          have h8n : 4 * (2 * n.toNat) < 2 ^ 64 := by omega
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h12n, Nat.mod_eq_of_lt h8n] at h4n
          simp [radixSrcOff] at h4n; omega
        · exact hJtmp (idx1P, ()) m1 ⟨rfl, hidx1⟩
      · cases use0
        · exact hJtmp (idx0P, ()) m1 ⟨rfl, hidx0⟩
        · exfalso; apply hc; rw [hsrc_eq]
          simpa [radixSrcOff] using hidx0.symm)

private theorem sort_reds_heap_branch {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} {n : BitVec 64} {m : Mem 64}
    (hSift : ∀ a m Q X, Full.fullRedSiftSpec a m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] a m Q X)
    (hrr_len : s.scratch.red_refs.length = c.red_cap)
    (hsb_len : s.scratch.scratch_buf.length = c.scratch_cap)
    (har_len : s.core.arena.length = c.arena_cap)
    (hrefs : ∀ j < n.toNat, (s.scratch.red_refs[j]?.getD 0#32).toNat + 2 < c.arena_cap)
    (hn_cap : n.toNat ≤ c.red_cap) (hn62 : n.toNat < 2 ^ 62) (hn_gt1 : 1 < n.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (rr' sb' : List (BitVec 32)) (m' : Mem 64),
      rr'.length = c.red_cap → sb'.length = c.scratch_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := sb' } } ⋆ R)
        m' →
      Q () m') :
    wp Γ Q X (Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p_11 =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var p_11.fst, Arg.imm 0, ()))
          fun p_12 =>
        Expr.jnz (Arg.var p_12.fst)
          (Expr.let_ (Op.mk (.sub i64) (Arg.var p_11.fst, Arg.imm 1, ())) fun p_13 =>
            Expr.call (as := [i64, i64, i64, i64]) (bs := []) "full_red_sift"
              (Arg.var c.pArena, Arg.var c.pRedRefs, Arg.var p_13.fst, Arg.var n, ()) fun _ =>
            Expr.jump Js.fst (Arg.var p_13.fst, ()))
          (Expr.let_ (Op.mk (.sub i64) (Arg.var n, Arg.imm 1, ())) fun p =>
            Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p =>
              Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                fun p_13 =>
              Expr.jnz (Arg.var p_13.fst)
                (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p_14 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_14.fst, Arg.imm 4, ())) fun p_15 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_15.fst, ()))
                    fun p_16 =>
                  Expr.load i32 (Arg.var p_16.fst) fun ld_3 =>
                  Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p_17 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_17.fst, Arg.imm 4, ())) fun p_18 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_18.fst, ()))
                    fun p_19 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_20 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_20.fst, ()))
                    fun p_21 =>
                  Expr.load i32 (Arg.var p_21.fst) fun ld_4 =>
                  Expr.store (t := i32) (Arg.var ld_4) (Arg.var p_19.fst)
                    (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_22 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_22.fst, ()))
                        fun p_23 =>
                      Expr.store (t := i32) (Arg.var ld_3) (Arg.var p_23.fst)
                        (Expr.call (as := [i64, i64, i64, i64]) (bs := []) "full_red_sift"
                          (Arg.var c.pArena, Arg.var c.pRedRefs, Arg.imm 0, Arg.var p.fst, ())
                          fun _ =>
                          Expr.let_ (Op.mk (.sub i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                            Expr.jump Js.fst (Arg.var p.fst, ()))))
                (Expr.ret ())) Blocks.nil)
              fun Js => Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var (n >>> (1 : Nat), ()).fst, ())) m := by
  refine wp_loop_inv (fun (st, ()) m1 => insOuterInv c s R n.toNat st m1)
      (fun (st, ()) _ => st.toNat)
      (fun J1 hLoop1 => by
        have hst0 : (n >>> (1 : Nat)).toNat ≤ n.toNat := by
          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
        exact hLoop1 (n >>> (1 : Nat), ()) m
          ⟨hst0, s.scratch.red_refs, hrr_len, fun k hk => ⟨k, hk, rfl⟩, hm⟩)
      (fun J1 (st, ()) m1 ⟨hst_le, rr1, hlen1, hmem1, hm1⟩ hLoop1 => by
        c0_hfast
        · have hst_pos : 0 < st.toNat := by c0_bound
          have hst1_eq : (st - 1).toNat = st.toNat - 1 := bv64_pred_toNat st hst_pos
          c0_call hSift
          let s1 := { s with scratch := { s.scratch with red_refs := rr1 } }
          refine ⟨s.core.arena, rr1, FullArenaRedRest c s1 ⋆ R,
            by dsimp only [Arg.val]; rw [hst1_eq]; omega,
            by dsimp only [Arg.val]; omega, hn62, fun k hk => ?_,
            focus_full_arena_red_refs hm1, fun rr2 m2 hlen2 _ hmem2 hm2 => ?_⟩
          · obtain ⟨j, hj, heq⟩ := hmem1 k hk; rw [heq, har_len]; exact hrefs j hj
          · c0_hfast
            refine hLoop1 (st - 1, ()) m2 (by dsimp only; rw [hst1_eq]; omega)
              ⟨by rw [hst1_eq]; omega, rr2, by omega, fun k hk => ?_, ?_⟩
            · obtain ⟨j, hj, heq⟩ := hmem2 k hk; obtain ⟨j0, hj0, heq0⟩ := hmem1 j hj
              exact ⟨j0, hj0, heq.trans heq0⟩
            · simpa [s1] using unfocus_full_arena_red_refs hm2
        · refine wp_loop_inv
            (fun (ed, ()) m2 => ed.toNat < n.toNat ∧ ∃ rr2 : List (BitVec 32),
              rr2.length = c.red_cap ∧
              (∀ k < n.toNat, ∃ j < n.toNat, rr2[k]? = s.scratch.red_refs[j]?) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rr2 } } ⋆ R) m2)
            (fun (ed, ()) _ => ed.toNat)
            (fun J2 hLoop2 => by
              have hn1 := bv64_pred_toNat n (by omega)
              exact hLoop2 (n - 1#64, ()) m1 ⟨by rw [hn1]; omega, rr1, hlen1, hmem1, hm1⟩)
            (fun J2 (ed, ()) m2 ⟨hed_lt, rr2, hlen2, hmem2, hm2⟩ hLoop2 => by
              c0_hfast
              · have hed_pos : 0 < ed.toNat := by c0_bound
                have h0_rr : 0 < rr2.length := by omega
                have hed_rr : ed.toNat < rr2.length := by omega
                c0_hfast; c0_call hSift
                dsimp only [fullRedSiftSpec, vals, Arg.val]
                let rr_sw := (rr2.set 0 (rr2[ed.toNat]'hed_rr)).set ed.toNat (rr2[0]'h0_rr)
                let s_sw := { s with scratch := { s.scratch with red_refs := rr_sw } }
                have hmem_sw := heap_swap_mem h0_rr hed_rr hed_lt hmem2
                refine ⟨s.core.arena, rr_sw, FullArenaRedRest c s_sw ⋆ R, Nat.zero_le _,
                  by simp [rr_sw, hlen2]; omega, by omega, fun k hk => ?_,
                  focus_full_arena_red_refs
                    (by first | assumption | (dsimp only [s_sw, rr_sw]; assumption)),
                  fun rr3 m3 hlen3 hout3 hmem3 hm3 => ?_⟩
                · obtain ⟨j, hj, heq⟩ := hmem_sw k (by omega)
                  rw [heq, har_len]; exact hrefs j hj
                · have hed1_eq : (ed - 1).toNat = ed.toNat - 1 := bv64_pred_toNat ed hed_pos
                  c0_hfast
                  refine hLoop2 (ed - 1, ()) m3 (by dsimp only; rw [hed1_eq]; omega)
                    ⟨by rw [hed1_eq]; omega, rr3, by simp [rr_sw, hlen2] at hlen3; omega,
                      fun k hk => ?_, ?_⟩
                  · by_cases hke : k < ed.toNat
                    · obtain ⟨j, hj, heq⟩ := hmem3 k hke
                      obtain ⟨j0, hj0, heq0⟩ := hmem_sw j (by omega)
                      exact ⟨j0, hj0, heq.trans heq0⟩
                    · obtain ⟨j0, hj0, heq0⟩ := hmem_sw k hk
                      exact ⟨j0, hj0, (hout3 k (by omega)).trans heq0⟩
                  · simpa [s_sw] using unfocus_full_arena_red_refs hm3
              · exact hQ rr2 s.scratch.scratch_buf m2 hlen2 hsb_len hmem2 hm2))

theorem full_sort_reds_s5_wp (Γ : Env)
    (hSift : ∀ a m Q X, Full.fullRedSiftSpec a m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, step13SortRedsSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_sort_reds_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn_cap, hrefs, hm, hQ⟩
  have hrr_len := hlen.scratch_ok.red_refs_len
  have hsb_len := hlen.scratch_ok.scratch_buf_len
  have har_len := hlen.core_ok.arena_len_arr
  have hred_lt : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hn62 : n.toNat < 2 ^ 62 := by omega
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_sort_reds_body
  c0_hfast
  · exact hQ s.scratch.red_refs s.scratch.scratch_buf m hrr_len hsb_len
      (fun k hk => ⟨k, hk, rfl⟩) hm
  · have hn_gt1 : 1 < n.toNat := by
      have h1 : ¬ n.toNat ≤ BitVec.toNat (1#64) := by assumption
      exact Nat.lt_of_not_le h1
    have hn_lt32 : n.toNat < 32 := by c0_bound
    refine wp_loop_inv (fun (i, ()) m1 => insOuterInv c s R n.toNat i m1)
        (fun (i, ()) _ => n.toNat - i.toNat)
        (fun J1 hJ1 => hJ1 (1#64, ()) m ⟨by rw [show (1#64).toNat = 1 from rfl]; omega,
          s.scratch.red_refs, hrr_len, fun k hk => ⟨k, hk, rfl⟩, hm⟩)
        (fun J1 (i, ()) m1 ⟨hi_le, rr1, hlen1, hmem1, hm1⟩ hJ1 => by
          c0_hfast
          · have hi_lt : i.toNat < n.toNat := by c0_bound
            have hi_rr : i.toNat < rr1.length := by omega
            obtain ⟨jx, hjx, hxeq⟩ := hmem1 i.toNat hi_lt
            have hxb := hrefs jx hjx
            rw [← hxeq, List.getElem?_eq_getElem hi_rr, Option.getD_some] at hxb
            have hx0 := bv32_zext64_eq (rr1[i.toNat]'hi_rr)
            have hx_ar : ((rr1[i.toNat]'hi_rr).setWidth 64).toNat < s.core.arena.length := by
              rw [hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
            have hx2_ar : ((rr1[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                s.core.arena.length := by
              rw [hx0, bv64_add_nat 2 (by decide) (by rw [BitVec.toNat_ofNat]; omega),
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
            c0_hfast
            refine wp_loop_inv (fun (j, ()) m2 => insInnerInv c s R n.toNat i.toNat j m2)
              (fun (j, ()) _ => j.toNat)
              (fun J2 hJ2 => hJ2 (i, ()) m1
                ⟨Nat.le_refl _, rr1, hlen1, fun k hk _ => hmem1 k hk, hm1⟩)
              (fun J2 (j, ()) m2 ⟨hj_le, rr2, hlen2, hmem2, hm2⟩ hJ2 => by
                have hj_rr : j.toNat < rr2.length := by omega
                have hj_rr' : j.toNat < ({ s with scratch :=
                    { s.scratch with red_refs := rr2 } }).scratch.red_refs.length := by
                  simpa using hj_rr
                have hi1 := bv64_succ_toNat i (by omega)
                c0_hfast
                · have hj_pos : 0 < j.toNat := by c0_bound
                  have hjm1 := bv64_pred_toNat j hj_pos
                  have hjm1_rr : (j - 1#64).toNat < rr2.length := by rw [hjm1]; omega
                  obtain ⟨jy, hjy, hyeq⟩ := hmem2 (j - 1#64).toNat (by rw [hjm1]; omega)
                    (by rw [hjm1]; omega)
                  have hyb := hrefs jy hjy
                  rw [← hyeq, List.getElem?_eq_getElem hjm1_rr, Option.getD_some] at hyb
                  have hy0 := bv32_zext64_eq (rr2[(j - 1#64).toNat]'hjm1_rr)
                  have hy_ar : ((rr2[(j - 1#64).toNat]'hjm1_rr).setWidth 64).toNat <
                      s.core.arena.length := by
                    rw [hy0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                  have hy2_ar : ((rr2[(j - 1#64).toNat]'hjm1_rr).setWidth 64 + 2#64).toNat <
                      s.core.arena.length := by
                    rw [hy0, bv64_add_nat 2 (by decide) (by rw [BitVec.toNat_ofNat]; omega),
                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                  c0_hfast
                  · refine hJ1 (i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega) ?_
                    exact ⟨by rw [hi1]; omega, rr2.set j.toNat _, by simp [hlen2],
                      ins_finish_step (by omega) (by omega) hi_rr hxeq hjx hmem2, by assumption⟩
                  · refine hJ2 (j - 1#64, ()) _ (by dsimp only; rw [hjm1]; omega) ?_
                    refine ⟨by rw [hjm1]; omega, rr2.set j.toNat _, by simp [hlen2],
                      fun k hk hne => ?_, by assumption⟩
                    exact ins_swap_step (by omega) (by omega)
                      (by dsimp only; rw [← hyeq, List.getElem?_eq_getElem]; rfl)
                      hmem2 hjy k hk (by omega)
                · refine hJ1 (i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega) ?_
                  exact ⟨by rw [hi1]; omega, rr2.set j.toNat _, by simp [hlen2],
                    ins_finish_step (by omega) (by omega) hi_rr hxeq hjx hmem2, by assumption⟩)
          · exact hQ rr1 s.scratch.scratch_buf m1 hlen1 hsb_len hmem1 hm1)
  · have hn_gt1 : 1 < n.toNat := by
      have h1 : ¬ n.toNat ≤ BitVec.toNat (1#64) := by assumption
      exact Nat.lt_of_not_le h1
    have hcap : 4 * n.toNat + 512 ≤ c.scratch_cap := by
      have hc' : (4 * n.toNat + 512) % 2 ^ 64 ≤ c.scratch_cap % 2 ^ 64 := hc
      rw [Nat.mod_eq_of_lt (by omega)] at hc'
      exact Nat.le_trans hc' (Nat.mod_le _ _)
    let idx0P := c.pScratchBuf + (2#64 * n) * 4#64
    let idx1P := idx0P + n * 4#64
    let cntP := c.pScratchBuf + (2#64 * n) * 8#64
    have ⟨hidx0, hidx1, _, hcnt_addr⟩ := radix_ptr_eqs c n (by omega)
    refine wp_loop_inv
        (fun (i, ()) m0 => i.toNat ≤ n.toNat ∧ ∃ sb0 : List (BitVec 32),
          sb0.length = c.scratch_cap ∧
          (∀ k < i.toNat, (sb0[2 * n.toNat + k]?.getD 0#32).toNat < n.toNat) ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := sb0 } } ⋆ R) m0)
        (fun (i, ()) _ => n.toNat - i.toNat)
        (fun L0 hL0 => hL0 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hsb_len,
          (fun _ h => by cases h), hm⟩)
        (fun L0 (i, ()) m0 ⟨hi_le, sb0, hlen0, hidx0_lt, hm0⟩ hL0 => by
            c0_msplit
            · have hi_lt : i.toNat < n.toNat := by c0_bound
              have hi_rr : i.toNat < s.scratch.red_refs.length := by omega
              have hrb := hrefs i.toNat hi_lt
              rw [List.getElem?_eq_getElem hi_rr, Option.getD_some] at hrb
              have hr0 := bv32_zext64_eq (s.scratch.red_refs[i.toNat]'hi_rr)
              have hr_ar : ((s.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                  s.core.arena.length := by
                rw [hr0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
              have hr2_ar : ((s.scratch.red_refs[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                  s.core.arena.length := by
                rw [hr0, bv64_add_nat 2 (by decide) (by rw [BitVec.toNat_ofNat]; omega),
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
              c0_hfast
              obtain ⟨hok1, hok2, hln', hlt', hst⟩ :=
                radix_init_step _ rfl hlen0 hcap hi_lt (by omega) hidx0 hidx0_lt hm0
              have hi1 := bv64_succ_toNat i (by omega)
              refine ⟨hok1, by decide, hok2, hL0 (i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
                ⟨by rw [hi1]; omega, _, hln', by rw [hi1]; exact hlt', hst⟩⟩
            · c0_hstraight
              refine wp_loop_inv (fun (_, src, dst, shift, ()) m1 =>
                  radixOuterInv c s R n.toNat src dst shift m1)
                (fun (_, _, _, shift, ()) _ => 64 - shift.toNat)
                (fun Ls hLs => hLs (i, idx0P, idx1P, 0#64, ()) m0
                  ⟨Nat.zero_le _, rfl, true, sb0, hlen0, hidx0, hidx1,
                    fun k hk => hidx0_lt k (by omega), hm0⟩)
                (fun Ls (_, src, dst, shift, ()) m1
                    ⟨hsh_le, hsh_mod, use0, sb1, hlen1, hsrc_eq, hdst_eq, hsrc_lt, hm1⟩ hLs => by
                  c0_hfast_nogrp
                  · have hsh_lt : shift.toNat < 64 := by c0_bound
                    let keyFn : Nat → Nat := fun k => ((pairU64At sb1 (sb1[radixSrcOff use0
                      n.toNat + k]?.getD 0#32).toNat >>> shift.toNat) &&& 255#64).toNat
                    have hkey_lt : ∀ k < n.toNat, keyFn k < 256 := fun k _ => by
                      dsimp only [keyFn]; rw [BitVec.toNat_and, show (255#64).toNat = 255 from rfl]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    refine wp_loop_inv (fun (b, ()) m2 => radixZeroInv c s R n.toNat sb1 b m2)
                      (fun (b, ()) _ => 256 - b.toNat)
                      (fun Lb hLb => hLb (0#64, ()) m1 ⟨Nat.zero_le _, sb1, hlen1,
                        fun _ _ => rfl, (fun _ h => by cases h), hm1⟩)
                      (fun Lb (b, ()) m2 ⟨hb_le, sb2, hlen2, hpre2, hzr2, hm2⟩ hLb => by
                        c0_hfast
                        · have hb_lt : b.toNat < 256 := by c0_bound
                          have hb1 := bv64_succ_toNat b (by omega)
                          obtain ⟨hok, hln', hpre', hzr', hst⟩ :=
                            radix_zero_step (cntP := cntP) rfl hlen2 hcap hb_lt
                              (hcnt_addr b hb_lt) hpre2 hzr2 hm2
                          refine ⟨hok, hLb (b + 1#64, ()) _ (by dsimp only; rw [hb1]; omega)
                            ⟨by rw [hb1]; omega, _, hln', hpre',
                              by rw [hb1]; exact hzr', hst⟩⟩
                        · have hb_ge : 256 ≤ b.toNat := by
                            have h1 : ¬ b.toNat < BitVec.toNat (256#64) := by assumption
                            exact Nat.le_of_not_lt h1
                          refine wp_loop_inv
                            (fun (i, _, _, ()) m3 => radixCountInv c s R n.toNat sb1 keyFn i m3)
                            (fun (i, _, _, ()) _ => n.toNat - i.toNat)
                            (fun Li hLi => hLi (0#64, 255#64, 0#64, ()) m2
                              ⟨Nat.zero_le _, sb2, hlen2, hpre2,
                                fun k hk => by
                                  have hcp0 := countPrefix_le keyFn 0 k
                                  rw [hzr2 k (by omega), show (0#64).toNat = 0 from rfl]; omega,
                                hm2⟩)
                            (fun Li (i, lo, hi, ()) m3 ⟨hi_le, sb3, hlen3, hpre3, hcnt3, hm3⟩
                                hLi => by
                              c0_msplit
                              · try c0_hfast
                                have hi_lt : i.toNat < n.toNat := by c0_bound
                                obtain ⟨hld1, _, hld2, hrk_eq⟩ := radix_src_load rfl hlen3
                                  hcap hi_lt (by omega) hsrc_eq hsrc_lt
                                  (fun j hj => hpre3 j (by omega))
                                  (fun k hk => hpre3 _ (by cases use0 <;>
                                    simp [radixSrcOff] <;> omega)) hm3
                                try dsimp only [Arg.val]
                                rw [show BitVec.ofNat 64 i.toNat * 4#64 = i * 4 from by
                                  simp [BitVec.ofNat_toNat]] at hld1
                                refine ⟨_, hld1, ?_⟩
                                c0_hstraight
                                try dsimp only [Arg.val]
                                let sid := sb3[radixSrcOff use0 n.toNat + i.toNat]'(by
                                  rw [hlen3]; exact radixSrcOff_lt use0 hi_lt hcap)
                                dsimp only at hld2 hrk_eq
                                refine ⟨_, hld2, ?_⟩
                                c0_hstraight
                                try dsimp only [Arg.val]
                                let btv := (pairU64At sb3 sid.toNat >>> shift) &&& 255#64
                                have hbt_nat : btv.toNat = keyFn i.toNat := radix_btv_nat hrk_eq
                                have hbt_lt : btv.toNat < 256 := by
                                  rw [hbt_nat]; exact hkey_lt i.toNat hi_lt
                                obtain ⟨hld3, hok, hln3', hp', hc', hst⟩ := radix_count_step rfl
                                  hlen3 hcap hi_lt (by omega) hpre3 hcnt3 hbt_lt hbt_nat
                                  (hcnt_addr btv hbt_lt) hm3
                                have hi1 := bv64_succ_toNat i (by omega)
                                dsimp only [btv, sid] at hld3 hok
                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                refine ⟨_, hld3, ?_⟩
                                c0_hstraight
                                try dsimp only [Arg.val]
                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                refine ⟨hok, ?_⟩
                                c0_hfast
                                all_goals
                                  exact hLi (i + 1#64, _, _, ()) _
                                    (by dsimp only; rw [hi1]; omega)
                                    ⟨by rw [hi1]; omega, _, hln3', hp',
                                      by rw [hi1]; exact hc', hst⟩
                              · c0_hstraight
                                refine wp_join_group (ts := [i64, i64, i64, i64])
                                  (fun (_, src', dst', _, ()) m2 =>
                                    radixPassPost c s R n.toNat src' dst' m2)
                                  ?_ ?_
                                · rintro _ ⟨i', src', dst', _, ⟨⟩⟩ m2
                                    ⟨use0', sb2, hlen2, hsrc2, hdst2, hlt2, hm2⟩
                                  have hsh8 : (shift + 8#64).toNat = shift.toNat + 8 := by
                                    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
                                    exact Nat.mod_eq_of_lt (by omega)
                                  c0_hfast
                                  exact hLs (i', src', dst', shift + 8#64, ()) m2
                                    (by dsimp only; rw [hsh8]; omega)
                                    ⟨by rw [hsh8]; omega, by rw [hsh8]; omega,
                                      use0', sb2, hlen2, hsrc2, hdst2, hlt2, hm2⟩
                                · intro J hJ
                                  have hi_eq : i.toNat = n.toNat := by omega
                                  c0_hfast_nogrp
                                  · refine wp_loop_inv
                                      (fun (bp, pos, ()) m4 =>
                                        radixPrefInv c s R n.toNat sb1 keyFn bp pos m4)
                                      (fun (bp, _, ()) _ => 256 - bp.toNat)
                                      (fun Lp hLp => hLp (0#64, 0#64, ()) m3
                                        ⟨Nat.zero_le _, by rw [show (0#64).toNat = 0 from rfl,
                                          sumBuckets_zero], sb3, hlen3, hpre3,
                                          (fun _ h => by cases h),
                                          fun k _ hk => by
                                            have hck := hcnt3 k hk; rwa [hi_eq] at hck, hm3⟩)
                                      (fun Lp (bp, pos, ()) m4 ⟨hbp_le, hpos_eq, sb4, hlen4,
                                          hpre4, hpref4, hrem4, hm4⟩ hLp => by
                                        c0_hfast_nogrp
                                        · have hbp_lt : bp.toNat < 256 := by c0_bound
                                          have hbp1 := bv64_succ_toNat bp (by omega)
                                          obtain ⟨hld, hok, hpos1, hln4', hpa, hpb, hpc, hst⟩ :=
                                            radix_pref_step rfl hlen4 hcap (by omega) hkey_lt
                                              hbp_lt hpos_eq (hcnt_addr bp hbp_lt) hpre4 hpref4
                                              hrem4 hm4
                                          exact ⟨_, hld, hok, hLp (bp + 1#64, pos + _, ()) _
                                            (by dsimp only; rw [hbp1]; omega)
                                            ⟨by rw [hbp1]; omega, by rw [hbp1]; exact hpos1, _,
                                              hln4', hpa, by rw [hbp1]; exact hpb,
                                              by rw [hbp1]; exact hpc, hst⟩⟩
                                        · have hbp256 : bp.toNat = 256 := by
                                            have h1 : ¬ bp.toNat < BitVec.toNat (256#64) := by
                                              assumption
                                            simp only [BitVec.toNat_ofNat] at h1; omega
                                          refine wp_loop_inv
                                            (fun (is_, ()) m5 =>
                                              radixScatterInv c s R use0 n.toNat sb1 keyFn is_ m5)
                                            (fun (is_, ()) _ => n.toNat - is_.toNat)
                                            (fun Lsc hLsc => hLsc (0#64, ()) m4
                                              ⟨Nat.zero_le _, sb4, hlen4,
                                                fun j hj => hpre4 j (by omega),
                                                fun k hk => hpre4 _ (by cases use0 <;>
                                                  simp [radixSrcOff] <;> omega),
                                                fun b hb => by
                                                  have hcp0 := countPrefix_le keyFn 0 b
                                                  rw [hpref4 b (by omega),
                                                    show (0#64).toNat = 0 from rfl]
                                                  omega,
                                                fun b _ p h1 h2 => by
                                                  have hcp0 := countPrefix_le keyFn 0 b
                                                  rw [show (0#64).toNat = 0 from rfl] at h2
                                                  omega, hm4⟩)
                                            (fun Lsc (is_, ()) m5 ⟨his_le, sb5, hlen5, hrk5,
                                                hsr5, hcnt5, hdst5, hm5⟩ hLsc => by
                                              c0_hfast
                                              · have his_lt : is_.toNat < n.toNat := by c0_bound
                                                obtain ⟨hld1, hid_lt, hld2, hrk_eq⟩ :=
                                                  radix_src_load rfl hlen5 hcap his_lt (by omega)
                                                    hsrc_eq hsrc_lt hrk5 hsr5 hm5
                                                try dsimp only [Arg.val]
                                                rw [show BitVec.ofNat 64 is_.toNat * 4#64 = is_ * 4
                                                    from by simp [BitVec.ofNat_toNat]] at hld1
                                                refine ⟨_, hld1, ?_⟩
                                                c0_hstraight
                                                try dsimp only [Arg.val]
                                                let id32 := sb5[radixSrcOff use0 n.toNat +
                                                  is_.toNat]'(by
                                                    rw [hlen5]
                                                    exact radixSrcOff_lt use0 his_lt hcap)
                                                dsimp only at hld2 hrk_eq
                                                refine ⟨_, hld2, ?_⟩
                                                c0_hstraight
                                                try dsimp only [Arg.val]
                                                let btv := (pairU64At sb5 id32.toNat >>>
                                                  shift) &&& 255#64
                                                have hbt_nat : btv.toNat = keyFn is_.toNat :=
                                                  radix_btv_nat hrk_eq
                                                have hbt_lt : btv.toNat < 256 := by
                                                  rw [hbt_nat]; exact hkey_lt is_.toNat his_lt
                                                obtain ⟨hld3, hok1, hok2, hln', ha, hb, hc, hd,
                                                    hst⟩ :=
                                                  radix_scatter_step rfl hlen5 hcap (by omega)
                                                    hkey_lt hdst_eq (hcnt_addr btv hbt_lt) hrk5
                                                    hsr5 hcnt5 hdst5 hbt_lt hbt_nat his_lt hid_lt
                                                    hm5
                                                have hld4 := radix_scatter_reload id32 rfl hlen5
                                                  hcap (by omega) hkey_lt hdst_eq
                                                  (hcnt_addr btv hbt_lt) hcnt5 hbt_lt hbt_nat
                                                  his_lt hm5
                                                have his1 := bv64_succ_toNat is_ (by omega)
                                                dsimp only [btv] at hld3 hok1 hld4 hok2 hst
                                                dsimp only [id32] at hld3 hok1 hld4 hok2 hst
                                                rw [BitVec.ofNat_toNat] at hok1 hok2 hst
                                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                                refine ⟨_, hld3, ?_⟩
                                                c0_hstraight
                                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                                refine ⟨hok1, ?_⟩
                                                c0_hstraight
                                                try simp only [Arg.val]
                                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                                refine ⟨_, hld4, ?_⟩
                                                c0_hstraight
                                                try rw [Nat.mod_eq_of_lt hsh_lt]
                                                refine ⟨hok2, ?_⟩
                                                c0_hfast
                                                exact hLsc (is_ + 1#64, ()) _
                                                  (by dsimp only; rw [his1]; omega)
                                                  ⟨by rw [his1]; omega, _, hln', ha, hb,
                                                    by rw [his1]; exact hc,
                                                    by rw [his1]; exact hd,
                                                    by
                                                      try simp only [Arg.val]
                                                      try rw [Nat.mod_eq_of_lt hsh_lt]
                                                      exact hst⟩
                                              · exact hJ (is_, dst, src, bp, ()) m5
                                                  ⟨!use0, sb5, hlen5,
                                                    by cases use0 <;> simp [radixSrcOff] <;>
                                                      assumption,
                                                    by cases use0 <;> simp [radixDstOff] <;>
                                                      assumption,
                                                    fun p hp => by
                                                      obtain ⟨b, hb, hp1, hp2⟩ :=
                                                        sumBuckets_cover keyFn n.toNat hkey_lt hp
                                                      have his_eq : is_.toNat = n.toNat := by omega
                                                      have := hdst5 b hb p hp1
                                                        (by rw [his_eq]; exact hp2)
                                                      cases use0 <;>
                                                        simp [radixSrcOff, radixDstOff]
                                                          at this ⊢ <;>
                                                        exact this, hm5⟩))
                                  · exact hJ (i, src, dst, b, ()) m3
                                      ⟨use0, sb3, hlen3, hsrc_eq, hdst_eq,
                                        fun k hk => by
                                          rw [hpre3 _ (by cases use0 <;> simp [radixSrcOff] <;>
                                            omega)]
                                          exact hsrc_lt k hk, hm3⟩))
                  · exact sort_reds_radix_copy_tail hrr_len hn_cap hcap hred_lt (by omega) hlen1
                      hidx0 hidx1 hsrc_eq hsrc_lt hm1 hQ))
  · clear hc
    have hn_gt1 : 1 < n.toNat := by
      have h1 : ¬ n.toNat ≤ BitVec.toNat (1#64) := by assumption
      exact Nat.lt_of_not_le h1
    exact sort_reds_heap_branch hSift hrr_len hsb_len har_len hrefs hn_cap hn62 hn_gt1 hm hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
