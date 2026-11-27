/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.FullSpec2
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 1b (`dense_bin_roundtrip`,
`dense_bin_sort_roundtrip`)

Parametric `(Γ : Env)` proofs (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_dense_bin_roundtrip_fid_s13_wp` (`step13DenseBinRoundtripSpec`)
2. `full_dense_bin_sort_roundtrip_fid_s13_wp` (`step13DenseBinSortRoundtripSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "s13a1b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local elab "c0_hsplit_np_nobound" : tactic => do
  let _ ← LeanQbe.T.C0HeadStep.headSteps
    { unrollGroup := false, splitJnz := false, pruneJnz := false, useBound := false } 2000
  let _ ← LeanQbe.T.C0HeadStep.headStepOnce
    { unrollGroup := false, splitJnz := true, pruneJnz := false, useBound := false }

private inductive S13SliceContainsBin (k : FullCoreState) : Nat → Nat → Nat → Prop
  | here {p rem : Nat} {w0 : BitVec 32} (hrem : 0 < rem)
      (hw0 : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
      S13SliceContainsBin k p rem (w0 &&& 0x7FFFFFFF#32).toNat
  | step_bin {p rem x : Nat} {w0 : BitVec 32} (hrem : 0 < rem)
      (hw0 : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
      S13SliceContainsBin k (p + 1) (rem - 1) x → S13SliceContainsBin k p rem x
  | step_nonbin {p rem x : Nat} {w0 : BitVec 32} (hrem : 2 ≤ rem)
      (hw0 : k.wstk[p]? = some w0) (hnb : (w0 &&& 0x80000000#32) = 0#32) :
      S13SliceContainsBin k (p + 2) (rem - 2) x → S13SliceContainsBin k p rem x

private theorem s13_sliceContainsBin_zero {k : FullCoreState} {p x : Nat}
    (h : S13SliceContainsBin k p 0 x) : False := by
  cases h <;> omega

private theorem s13_bv64_shl1 (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  rw [show (x <<< 1#64) = x <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega

private theorem s13_bv64_shl1_add1 (x : BitVec 64) (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, s13_bv64_shl1 x (by omega), show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt hx]

private theorem s13_sliceContainsBin_bin_ne {k : FullCoreState} {p rem x : Nat}
    {w0 : BitVec 32} (h : S13SliceContainsBin k p rem x) (hw : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : x ≠ (w0 &&& 0x7FFFFFFF#32).toNat) :
    S13SliceContainsBin k (p + 1) (rem - 1) x := by
  cases h with
  | here _ hw' _ => rw [hw] at hw'; cases Option.some.inj hw'; exact absurd rfl hne
  | step_bin _ _ _ h1 => exact h1
  | step_nonbin _ hw' hnb => rw [hw] at hw'; cases Option.some.inj hw'; exact absurd hnb hbin

private theorem s13_sliceContainsBin_nonbin {k : FullCoreState} {p rem x : Nat}
    {w0 : BitVec 32} (h : S13SliceContainsBin k p rem x) (hw : k.wstk[p]? = some w0)
    (hnb : (w0 &&& 0x80000000#32) = 0#32) :
    S13SliceContainsBin k (p + 2) (rem - 2) x := by
  cases h with
  | here _ hw' hbin => rw [hw] at hw'; cases Option.some.inj hw'; exact absurd hnb hbin
  | step_bin _ hw' hbin _ => rw [hw] at hw'; cases Option.some.inj hw'; exact absurd hnb hbin
  | step_nonbin _ _ _ h1 => exact h1

private def clearLmExpr {V : Ty → Type} {K : List Ty → Type}
    (pwstk plm : V i64) (nlits off end_ nb : V i64) (ov : V .bool)
    (Jout : K [i64, .bool]) : Expr V K [] :=
  Expr.group (sig := [[i64]]) (fun Js_3 =>
    Blocks.cons (fun (p, ()) =>
      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p, Arg.var end_, ())) (fun (bp, ()) =>
      Expr.jnz (Arg.var bp)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var p, Arg.imm 4, ())) (fun (op, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pwstk, Arg.var op, ())) (fun (ap, ()) =>
        Expr.load i32 (Arg.var ap) (fun w0 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 1, ())) (fun (p1, ()) =>
        Expr.group (sig := [[i64]]) (fun _Js =>
          Blocks.cons (fun (pn, ()) => Expr.jump Js_3.fst (Arg.var pn, ())) Blocks.nil)
          (fun Js =>
          Expr.let_ (Op.mk (.and i32) (Arg.var w0, Arg.imm 0x80000000, ())) (fun (bw, ()) =>
          Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var bw, Arg.imm 0, ())) (fun (bb, ()) =>
          Expr.jnz (Arg.var bb)
            (Expr.let_ (Op.mk (.and i32) (Arg.var w0, Arg.imm 0x7FFFFFFF, ())) (fun (ot, ()) =>
            Expr.group (sig := [[]]) (fun _Js_4 =>
              Blocks.cons (fun _ => Expr.jump Js.fst (Arg.var p1, ())) Blocks.nil)
              (fun Js_4 =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64, ()) =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var ot64, Arg.var nlits, ()))
                (fun (bot, ()) =>
              Expr.jnz (Arg.var bot)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64b, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var plm, Arg.var ot64b, ())) (fun (alm, ()) =>
                Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
                Expr.store (Arg.var z8) (Arg.var alm) (Expr.jump Js_4.fst ())))))
                (Expr.jump Js_4.fst ()))))))
            (Expr.group (sig := [[i64]]) (fun _Js_4 =>
              Blocks.cons (fun (pn, ()) => Expr.jump Js.fst (Arg.var pn, ())) Blocks.nil)
              (fun Js_4 =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p1, Arg.var end_, ()))
                (fun (bp1, ()) =>
              Expr.jnz (Arg.var bp1)
                (Expr.let_ (Op.mk (.add i64) (Arg.var p1, Arg.imm 1, ())) (fun (p2, ()) =>
                Expr.jump Js_4.fst (Arg.var p2, ())))
                (Expr.jump Js_4.fst (Arg.var p1, ())))))))))))))
        (Expr.jump Jout (Arg.var nb, Arg.var ov, ()))))
    Blocks.nil) (fun Js_3 => Expr.jump Js_3.fst (Arg.var off, ()))

private theorem s13_bin_roundtrip_clear_lm_wp {Γ : Env} {Q : Post []}
    {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {l_lit : Nat} {off sz : BitVec 64} {lm0 : List (BitVec 8)}
    {nb : Val i64} {ov : Val .bool} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Jout : Cont [i64, .bool]}
    (hlen : { s with core := { s.core with lit_mark := lm0 } }.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hl_lt : l_lit < 2 * s.core.cur_vars)
    (hoff : off.toNat = fullWatchOffCore s.core l_lit)
    (hsz : sz.toNat = fullWatchSizeCore s.core l_lit)
    (hdirty : ∀ x < 2 * s.core.cur_vars,
      lm0[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x)
    (hhi : ∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lm0[x]?.getD 0#8 = 0#8)
    (hm0 : (FullMem c { s with core := { s.core with lit_mark := lm0 } } ⋆ R) m0)
    (hJout : ∀ (lmF : List (BitVec 8)) (mF : Mem 64),
      lmF.length = 2 * c.max_vars → (∀ x < 2 * c.max_vars, lmF[x]?.getD 0#8 = 0#8) →
      (FullMem c { s with core := { s.core with lit_mark := lmF } } ⋆ R) mF →
      Jout (nb, ov, ()) mF) :
    let end_ : BitVec 64 := off + sz
    let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< 1#64
    wp Γ Q X (clearLmExpr c.pWstk c.pLitMark nlits off end_ nb ov Jout) m0 := by
  intro end_ nlits
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hwl_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hmx_bd := c.hmaxv; unfold dimacsBound at hmx_bd
  have hlm_len : lm0.length = 2 * c.max_vars := hlen.core_ok.lit_mark_len
  have hws_len : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hws_bound := hw.watches.layout.bounds l_lit hl_lt
  have hws_lt32 : fullWatchOffCore s.core l_lit + fullWatchSizeCore s.core l_lit < 2 ^ 32 := by
    have := c.hwcap; unfold dimacsBound at this; omega
  have hend_eq : end_.toNat = off.toNat + sz.toNat := by dsimp only [end_]; bv_omega
  have hnlits : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [s13_bv64_shl1 _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold clearLmExpr
  refine wp_loop_inv (ts := [i64])
    (fun (p, ()) mP => p.toNat ≤ end_.toNat ∧
      ∃ rem lmP, p.toNat + rem = end_.toNat ∧ S13ModeSliceOk F_cur s.core l_lit p.toNat rem ∧
      lmP.length = 2 * c.max_vars ∧
      (∀ x < 2 * s.core.cur_vars, lmP[x]? ≠ some 0#8 → S13SliceContainsBin s.core p.toNat rem x) ∧
      (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lmP[x]?.getD 0#8 = 0#8) ∧
      (FullMem c { s with core := { s.core with lit_mark := lmP } } ⋆ R) mP)
    (fun (p, ()) _ => end_.toNat - p.toNat)
    (fun Js_3 hLoop => by
      c0_hsteps_nogrp
      refine hLoop (off, ()) m0 ⟨by omega, sz.toNat, lm0, by omega, ?_, hlm_len, hdirty, hhi, hm0⟩
      rw [hoff, hsz]; exact s13_modeSlice_of_inv hw.watches hl_lt)
    (fun Js_3 ⟨p, ⟨⟩⟩ mP ⟨hp_le, rem, lmP, hpr, hslice, hlmP_len, hdirtyP, hhiP, hmP⟩ hLoop => ?_)
  c0_hsplit
  · have hp_lt : p.toNat < end_.toNat := hc
    have hrem_pos : 0 < rem := by omega
    have hp_ws : p.toNat < s.core.wstk.length := by omega
    have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (pn, ()) mN => pn.toNat ≤ end_.toNat ∧ p.toNat < pn.toNat ∧
        ∃ remN lmN, pn.toNat + remN = end_.toNat ∧
        S13ModeSliceOk F_cur s.core l_lit pn.toNat remN ∧ lmN.length = 2 * c.max_vars ∧
        (∀ x < 2 * s.core.cur_vars,
          lmN[x]? ≠ some 0#8 → S13SliceContainsBin s.core pn.toNat remN x) ∧
        (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lmN[x]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with lit_mark := lmN } } ⋆ R) mN)
      (fun _ ⟨pn, ⟨⟩⟩ mN ⟨hpn_le, hpgt, remN, lmN, hprN, hsN, hlmN, hdirtyN, hhiN, hmN⟩ => by
        c0_hsteps_nogrp
        exact hLoop (pn, ()) mN (by dsimp only; omega)
          ⟨hpn_le, remN, lmN, hprN, hsN, hlmN, hdirtyN, hhiN, hmN⟩)
      (fun Js hJs => by
        c0_hsteps_nogrp; c0_hsplit
        · have hbin := hc
          have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_ws) :=
            List.getElem?_eq_getElem hp_ws
          obtain ⟨_, hot_lt, _, hslice1⟩ := s13_modeSlice_step_bin hslice hrem_pos hw0_eq hbin
          let ot := s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32
          have hot_toNat : ot.toNat < 2 * s.core.cur_vars := hot_lt
          have hot_lm : (ot.setWidth 64).toNat < lmP.length := by
            rw [hlmP_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m4 => ∃ lm4, lm4.length = 2 * c.max_vars ∧
              (∀ x < 2 * s.core.cur_vars,
                lm4[x]? ≠ some 0#8 → S13SliceContainsBin s.core (p.toNat + 1) (rem - 1) x) ∧
              (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lm4[x]?.getD 0#8 = 0#8) ∧
              (FullMem c { s with core := { s.core with lit_mark := lm4 } } ⋆ R) m4)
            (fun _ ⟨⟩ m4 ⟨lm4, hlm4, hdirty4, hhi4, hm4⟩ => by
              c0_hsteps_nogrp
              exact hJs (p + 1#64, ()) m4
                ⟨by omega, by omega, rem - 1, lm4, by omega, hp1_eq ▸ hslice1, hlm4,
                  fun x hx hne => hp1_eq ▸ hdirty4 x hx hne, hhi4, hm4⟩)
            (fun Js_4 hJs4 => by
              c0_hsteps_nogrp; c0_hsplit
              · have hot64_lt : (ot.setWidth 64).toNat <
                    ({ s with core := { s.core with lit_mark := lmP } }).core.lit_mark.length :=
                  hot_lm
                c0_hsteps_nogrp
                refine hJs4 () _ ⟨lmP.set (ot.setWidth 64).toNat 0#8, by simp [hlmP_len], ?_, ?_,
                  by assumption⟩
                · intro x hx hne
                  have he : (ot.setWidth 64).toNat = ot.toNat := by
                    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                  have hne_ot : x ≠ ot.toNat := fun heq => by
                    subst heq; apply hne; rw [he, List.getElem?_set_self (by omega)]
                  have hx_old : lmP[x]? ≠ some 0#8 := fun heq => by
                    apply hne; rw [List.getElem?_set_ne (by rw [he]; exact hne_ot.symm)]; exact heq
                  exact s13_sliceContainsBin_bin_ne (hdirtyP x hx hx_old) hw0_eq hbin hne_ot
                · intro x hx1 hx2
                  have he : (ot.setWidth 64).toNat = ot.toNat := by
                    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                  rw [List.getElem?_set_ne (by rw [he]; omega)]; exact hhiP x hx1 hx2)
        · have hnb := hc
          have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_ws) :=
            List.getElem?_eq_getElem hp_ws
          obtain ⟨hrem2, _, hslice2⟩ := s13_modeSlice_step_nonbin hslice hrem_pos hw0_eq hnb
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (pn, ()) m4 => pn.toNat = p.toNat + 2 ∧ m4 = mP)
            (fun _ ⟨pn, ⟨⟩⟩ m4 ⟨hpn2, hm4⟩ => by
              subst m4; c0_hsteps_nogrp
              refine hJs (pn, ()) mP ⟨by omega, by omega, rem - 2, lmP, by omega, hpn2 ▸ hslice2,
                hlmP_len,
                fun x hx hne => hpn2 ▸ s13_sliceContainsBin_nonbin (hdirtyP x hx hne) hw0_eq hnb,
                hhiP, hmP⟩)
            (fun Js_4 hJs4 => by
              c0_hsteps_nogrp; c0_hsplit
              · have hp2_eq : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
                c0_hsteps_nogrp; exact hJs4 (p + 1#64 + 1#64, ()) mP ⟨hp2_eq, rfl⟩))
  · have hrem0 : rem = 0 := by omega
    subst hrem0
    have hclean : ∀ x < 2 * c.max_vars, lmP[x]?.getD 0#8 = 0#8 := fun x hx => by
      by_cases hlt : x < 2 * s.core.cur_vars
      · have h0 : lmP[x]? = some 0#8 := Classical.byContradiction fun hne =>
          s13_sliceContainsBin_zero (hdirtyP x hlt hne)
        rw [h0]; rfl
      · exact hhiP x (Nat.le_of_not_lt hlt) hx
    c0_hsteps_nogrp; exact hJout lmP mP hlmP_len hclean hmP

private def scanSliceExpr {V : Ty → Type} {K : List Ty → Type}
    (pwstk pvals plm pscr : V i64) (nlits scap_pairs l off end_ nb0 : V i64)
    (lv : V i8) (ov_in : V .bool) (Ja2 : K [i64, .bool, i64]) : Expr V K [] :=
  Expr.group (sig := [[i64, i64]]) (fun Js_2 =>
    Blocks.cons (fun st =>
      let nb := st.1; let p := st.2.1;
      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p, Arg.var end_, ())) (fun (bp, ()) =>
      Expr.jnz (Arg.var bp)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var p, Arg.imm 4, ())) (fun (op, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pwstk, Arg.var op, ())) (fun (ap, ()) =>
        Expr.load i32 (Arg.var ap) (fun w0 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 1, ())) (fun (p1, ()) =>
        Expr.group (sig := [[i64, .bool, i64]]) (fun _ =>
          Blocks.cons (fun st3 =>
            Expr.jump Js_2.fst (Arg.var st3.1, Arg.var st3.2.2.1, ())) Blocks.nil)
          (fun Js_3 =>
          Expr.let_ (Op.mk (.and i32) (Arg.var w0, Arg.imm 0x80000000, ())) (fun (bw, ()) =>
          Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var bw, Arg.imm 0, ())) (fun (bb, ()) =>
          Expr.jnz (Arg.var bb)
            (Expr.let_ (Op.mk (.and i32) (Arg.var w0, Arg.imm 0x7FFFFFFF, ())) (fun (ot, ()) =>
            Expr.group (sig := [[i64, .bool]]) (fun _ =>
              Blocks.cons (fun st4 =>
                Expr.jump Js_3.fst (Arg.var st4.1, Arg.var st4.2.1, Arg.var p1, ())) Blocks.nil)
              (fun Js_4 =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64, ()) =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var ot64, Arg.var nlits, ()))
                (fun (bot, ()) =>
              Expr.jnz (Arg.var bot)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64b, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var plm, Arg.var ot64b, ())) (fun (alm, ()) =>
                Expr.load i8 (Arg.var alm) (fun mk =>
                Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
                Expr.let_ (Op.mk (.zext 8 32) (Arg.var mk, ())) (fun (mk32, ()) =>
                Expr.let_ (Op.mk (.zext 8 32) (Arg.var z8, ())) (fun (z32, ()) =>
                Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var mk32, Arg.var z32, ()))
                  (fun (bmk, ()) =>
                Expr.jnz (Arg.var bmk)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64c, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var plm, Arg.var ot64c, ())) (fun (alm2, ()) =>
                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) (fun (o8, ()) =>
                  Expr.store (Arg.var o8) (Arg.var alm2)
                    (Expr.group (sig := [[i64, .bool]]) (fun _ =>
                      Blocks.cons (fun st5 =>
                        Expr.jump Js_4.fst (Arg.var st5.1, Arg.var st5.2.1, ())) Blocks.nil)
                      (fun Js_5 =>
                      Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8b, ()) =>
                      Expr.let_ (Op.mk (.sext 8 32) (Arg.var lv, ())) (fun (lv32, ()) =>
                      Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8b, ())) (fun (z32b, ()) =>
                      Expr.let_ (Op.mk (.cmp .sle i32 .bool rfl) (Arg.var lv32, Arg.var z32b, ()))
                        (fun (blv, ()) =>
                      Expr.jnz (Arg.var blv)
                        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64d, ()) =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var pvals, Arg.var ot64d, ()))
                          (fun (av, ()) =>
                        Expr.load i8 (Arg.var av) (fun ov =>
                        Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8c, ()) =>
                        Expr.let_ (Op.mk (.sext 8 32) (Arg.var ov, ())) (fun (ov32, ()) =>
                        Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8c, ())) (fun (z32c, ()) =>
                        Expr.let_ (Op.mk (.cmp .sle i32 .bool rfl)
                          (Arg.var ov32, Arg.var z32c, ())) (fun (bov, ()) =>
                        Expr.jnz (Arg.var bov)
                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ot, ())) (fun (ot64e, ()) =>
                          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var l, Arg.var ot64e, ()))
                            (fun (blot, ()) =>
                          Expr.jnz (Arg.var blot)
                            (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                              (Arg.var nb, Arg.var scap_pairs, ())) (fun (bsc, ()) =>
                            Expr.jnz (Arg.var bsc)
                              (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1a, ()) =>
                              Expr.let_ (Op.mk (.shl i64) (Arg.var nb, Arg.var c1a, ()))
                                (fun (nb2a, ()) =>
                              Expr.let_ (Op.mk (.mul i64) (Arg.var nb2a, Arg.imm 4, ()))
                                (fun (onb0, ()) =>
                              Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var onb0, ()))
                                (fun (anb0, ()) =>
                              Expr.let_ (Op.mk (.trunc 64 32) (Arg.var l, ())) (fun (l32, ()) =>
                              Expr.store (Arg.var l32) (Arg.var anb0)
                                (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
                                Expr.let_ (Op.mk (.shl i64) (Arg.var nb, Arg.var c1b, ()))
                                  (fun (nb2b, ()) =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var nb2b, Arg.imm 1, ()))
                                  (fun (nb2p, ()) =>
                                Expr.let_ (Op.mk (.mul i64) (Arg.var nb2p, Arg.imm 4, ()))
                                  (fun (onb1, ()) =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var onb1, ()))
                                  (fun (anb1, ()) =>
                                Expr.store (Arg.var ot) (Arg.var anb1)
                                  (Expr.let_ (Op.mk (.add i64) (Arg.var nb, Arg.imm 1, ()))
                                    (fun (nbn, ()) =>
                                  Expr.jump Js_5.fst
                                    (Arg.var nbn, Arg.var ov_in, ())))))))))))))))
                              (Expr.jump Ja2 (Arg.var nb, Arg.imm true, Arg.var p1, ()))))
                            (Expr.jump Js_5.fst (Arg.var nb, Arg.var ov_in, ())))))
                          (Expr.jump Js_5.fst (Arg.var nb, Arg.var ov_in, ()))))))))))
                        (Expr.jump Js_5.fst (Arg.var nb, Arg.var ov_in, ()))))))))))))
                  (Expr.jump Js_4.fst (Arg.var nb, Arg.var ov_in, ()))))))))))
                (Expr.jump Js_4.fst (Arg.var nb, Arg.var ov_in, ())))))))
            (Expr.group (sig := [[i64]]) (fun _ =>
              Blocks.cons (fun (pn, ()) =>
                Expr.jump Js_3.fst (Arg.var nb, Arg.var ov_in, Arg.var pn, ())) Blocks.nil)
              (fun Js_4 =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p1, Arg.var end_, ()))
                (fun (bp1, ()) =>
              Expr.jnz (Arg.var bp1)
                (Expr.let_ (Op.mk (.add i64) (Arg.var p1, Arg.imm 1, ())) (fun (p2, ()) =>
                Expr.jump Js_4.fst (Arg.var p2, ())))
                (Expr.jump Js_4.fst (Arg.var p1, ())))))))))))))
        (Expr.jump Ja2 (Arg.var nb, Arg.var ov_in, Arg.var p, ()))))
    Blocks.nil) (fun Js_2 => Expr.jump Js_2.fst (Arg.var nb0, Arg.var off, ()))

private theorem s13_bin_roundtrip_scan_slice_wp {Γ : Env} {Q : Post []}
    {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {l_lit : Nat} {l off sz nb0 : BitVec 64} {lm0 : List (BitVec 8)} {scr0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Ja2 : Cont [i64, .bool, i64]}
    (hlen : { s with core := { s.core with lit_mark := lm0 }
                     scratch := { s.scratch with scratch_buf := scr0 } }.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hl_eq : l.toNat = l_lit)
    (hl_lt : l_lit < 2 * s.core.cur_vars)
    (hoff : off.toNat = fullWatchOffCore s.core l_lit)
    (hsz : sz.toNat = fullWatchSizeCore s.core l_lit)
    (hlm_clr : ∀ x < 2 * c.max_vars, lm0[x]?.getD 0#8 = 0#8)
    (hbp0 : BinPairsOk c F_cur s nb0.toNat scr0)
    (hm0 : (FullMem c { s with core := { s.core with lit_mark := lm0 }
                               scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m0)
    (hJa2 : ∀ (nb' : BitVec 64) (ov' : Bool) (pfin : Val i64)
        (lm' : List (BitVec 8)) (scr' : List (BitVec 32)) (m' : Mem 64),
      lm'.length = 2 * c.max_vars → BinPairsOk c F_cur s nb'.toNat scr' →
      (∀ x < 2 * s.core.cur_vars,
        lm'[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x) →
      (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lm'[x]?.getD 0#8 = 0#8) →
      (FullMem c { s with core := { s.core with lit_mark := lm' }
                          scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Ja2 (nb', ov', pfin, ()) m') :
    let end_ : BitVec 64 := off + sz
    let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< 1#64
    let scap_pairs : BitVec 64 := BitVec.ofNat 64 c.scratch_cap >>> 1#64
    let lv : Val i8 := s.core.vals[l_lit]'(by
      have := c.hmaxv; unfold dimacsBound at this
      have hvl : s.core.vals.length = 2 * c.max_vars := hlen.core_ok.vals_len
      have hcl : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
      omega)
    wp Γ Q X (scanSliceExpr c.pWstk c.pVals c.pLitMark c.pScratchBuf
      nlits scap_pairs l off end_ nb0 lv false Ja2) m0 := by
  intro end_ nlits scap_pairs lv
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hwl_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hmx_bd := c.hmaxv; unfold dimacsBound at hmx_bd
  have hlm_len : lm0.length = 2 * c.max_vars := hlen.core_ok.lit_mark_len
  have hv_len : s.core.vals.length = 2 * c.max_vars := hlen.core_ok.vals_len
  have hws_len : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hws_bound := hw.watches.layout.bounds l_lit hl_lt
  have hws_lt32 : fullWatchOffCore s.core l_lit + fullWatchSizeCore s.core l_lit < 2 ^ 32 := by
    have := c.hwcap; unfold dimacsBound at this; omega
  have hend_eq : end_.toNat = off.toNat + sz.toNat := by dsimp only [end_]; bv_omega
  have hnlits : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [s13_bv64_shl1 _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hscap : scap_pairs.toNat = c.scratch_cap / 2 := by
    have := c.hscr; unfold dimacsBound at this
    dsimp only [scap_pairs]
    rw [show (BitVec.ofNat 64 c.scratch_cap >>> 1#64) =
        BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat) from rfl,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  unfold scanSliceExpr
  refine wp_loop_inv (ts := [i64, i64])
    (fun (nb, p, ()) mP => p.toNat ≤ end_.toNat ∧
      ∃ rem lmP scrP, p.toNat + rem = end_.toNat ∧
      S13ModeSliceOk F_cur s.core l_lit p.toNat rem ∧ lmP.length = 2 * c.max_vars ∧
      BinPairsOk c F_cur s nb.toNat scrP ∧
      (∀ x, S13SliceContainsBin s.core p.toNat rem x →
        S13SliceContainsBin s.core off.toNat sz.toNat x) ∧
      (∀ x < 2 * s.core.cur_vars,
        lmP[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x) ∧
      (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lmP[x]?.getD 0#8 = 0#8) ∧
      (FullMem c { s with core := { s.core with lit_mark := lmP }
                          scratch := { s.scratch with scratch_buf := scrP } } ⋆ R) mP)
    (fun (nb, p, ()) _ => end_.toNat - p.toNat)
    (fun Js_2 hLoop => by
      c0_hsteps_nogrp
      refine hLoop (nb0, off, ()) m0 ⟨by omega, sz.toNat, lm0, scr0, by omega, ?_, hlm_len, hbp0,
        fun _ hx => hx,
        fun x hx hne => absurd (by
          have h0 := hlm_clr x (by omega)
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
          rw [List.getElem?_eq_getElem (by omega), h0]) hne,
        fun x _ hx2 => hlm_clr x hx2, hm0⟩
      rw [hoff, hsz]; exact s13_modeSlice_of_inv hw.watches hl_lt)
    (fun Js_2 ⟨nb, p, ⟨⟩⟩ mP ⟨hp_le, rem, lmP, scrP, hpr, hslice, hlmP_len, hbpP, hsubP, hdirtyP,
        hhiP, hmP⟩ hLoop => ?_)
  c0_hsplit
  · have hp_lt : p.toNat < end_.toNat := hc
    have hrem_pos : 0 < rem := by omega
    have hp_ws : p.toNat < s.core.wstk.length := by omega
    have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64, .bool, i64])
      (fun (nbN, _ovN, pn, ()) mN => pn.toNat ≤ end_.toNat ∧ p.toNat < pn.toNat ∧
        ∃ remN lmN scrN, pn.toNat + remN = end_.toNat ∧
        S13ModeSliceOk F_cur s.core l_lit pn.toNat remN ∧ lmN.length = 2 * c.max_vars ∧
        BinPairsOk c F_cur s nbN.toNat scrN ∧
        (∀ x, S13SliceContainsBin s.core pn.toNat remN x →
          S13SliceContainsBin s.core off.toNat sz.toNat x) ∧
        (∀ x < 2 * s.core.cur_vars,
          lmN[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x) ∧
        (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lmN[x]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with lit_mark := lmN }
                            scratch := { s.scratch with scratch_buf := scrN } } ⋆ R) mN)
      (fun _ ⟨nbN, _ovN, pn, ⟨⟩⟩ mN
          ⟨hpn_le, hpgt, remN, lmN, scrN, hprN, hsN, hlmN, hbpN, hsubN, hdirtyN, hhiN, hmN⟩ => by
        c0_hsteps_nogrp
        exact hLoop (nbN, pn, ()) mN (by dsimp only; omega)
          ⟨hpn_le, remN, lmN, scrN, hprN, hsN, hlmN, hbpN, hsubN, hdirtyN, hhiN, hmN⟩)
      (fun Js_3 hJs3 => by
        c0_hsteps_nogrp; c0_hsplit
        · have hbin := hc
          have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_ws) :=
            List.getElem?_eq_getElem hp_ws
          obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
            s13_modeSlice_step_bin hslice hrem_pos hw0_eq hbin
          let ot := s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32
          have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
          have hsub1 : ∀ x, S13SliceContainsBin s.core (p.toNat + 1) (rem - 1) x →
              S13SliceContainsBin s.core off.toNat sz.toNat x := fun x hx =>
            hsubP x (.step_bin hrem_pos hw0_eq hbin hx)
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, .bool])
            (fun (nb4, ov4, ()) m4 => ov4 = false ∧ ∃ lm4 scr4, lm4.length = 2 * c.max_vars ∧
              BinPairsOk c F_cur s nb4.toNat scr4 ∧
              (∀ x < 2 * s.core.cur_vars,
                lm4[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x) ∧
              (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars → lm4[x]?.getD 0#8 = 0#8) ∧
              (FullMem c { s with core := { s.core with lit_mark := lm4 }
                                  scratch := { s.scratch with scratch_buf := scr4 } } ⋆ R) m4)
            (fun _ ⟨nb4, ov4, ⟨⟩⟩ m4 ⟨hov4, lm4, scr4, hlm4, hbp4, hdirty4, hhi4, hm4⟩ => by
              subst hov4; c0_hsteps_nogrp
              exact hJs3 (nb4, false, p + 1#64, ()) m4
                ⟨by omega, by omega, rem - 1, lm4, scr4, by omega, hp1_eq.symm ▸ hslice1, hlm4,
                  hbp4, fun x hx => hsub1 x (hp1_eq ▸ hx), hdirty4, hhi4, hm4⟩)
            (fun Js_4 hJs4 => by
              c0_hsplit_np_nobound
              · have hot_lm : (ot.setWidth 64).toNat <
                    ({ s with
                        core := { s.core with lit_mark := lmP }
                        scratch := { s.scratch with scratch_buf := scrP } }
                      ).core.lit_mark.length := by
                  dsimp only
                  rw [hlmP_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                c0_hsplit_np_nobound
                · let lm1 := lmP.set (ot.setWidth 64).toNat 1#8
                  have hlm1_len : lm1.length = 2 * c.max_vars := by simp [lm1, hlmP_len]
                  have hdirty1 : ∀ x < 2 * s.core.cur_vars,
                      lm1[x]? ≠ some 0#8 → S13SliceContainsBin s.core off.toNat sz.toNat x := by
                    intro x hx hne; dsimp only [lm1] at hne
                    by_cases hxot : x = (ot.setWidth 64).toNat
                    · subst hxot; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      exact hsubP ot.toNat (.here hrem_pos hw0_eq hbin)
                    · rw [List.getElem?_set_ne (by omega)] at hne; exact hdirtyP x hx hne
                  have hhi1 : ∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars →
                      lm1[x]?.getD 0#8 = 0#8 := by
                    intro x hx1 hx2; dsimp only [lm1]
                    have he : (ot.setWidth 64).toNat = ot.toNat := by
                      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                    rw [List.getElem?_set_ne (by rw [he]; omega)]; exact hhiP x hx1 hx2
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, .bool])
                    (fun (nb5, ov5, ()) m5 => ov5 = false ∧
                      ∃ scr5, BinPairsOk c F_cur s nb5.toNat scr5 ∧
                        (FullMem c { s with core := { s.core with lit_mark := lm1 }
                                            scratch := { s.scratch with scratch_buf := scr5 } } ⋆
                          R) m5)
                    (fun _ ⟨nb5, ov5, ⟨⟩⟩ m5 ⟨hov5, scr5, hbp5, hm5⟩ => by
                      subst hov5; c0_hsteps_nogrp
                      exact hJs4 (nb5, false, ()) m5
                        ⟨rfl, lm1, scr5, hlm1_len, hbp5, hdirty1, hhi1, hm5⟩)
                    (fun Js_5 hJs5 => by
                      c0_hsplit_np_nobound
                      · have hot_v : (ot.setWidth 64).toNat <
                            ({ s with core := { s.core with lit_mark := lm1 }
                                      scratch := { s.scratch with
                                        scratch_buf := scrP } }).core.vals.length := by
                          dsimp only
                          rw [hv_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                        c0_hsplit_np_nobound
                        · c0_hsplit_np_nobound
                          · c0_hsplit_np_nobound
                            · have hnb_lt : nb.toNat < c.scratch_cap / 2 := by
                                have h1 := hc; rwa [hscap] at h1
                              have hsc_len : scrP.length = c.scratch_cap := hbpP.1
                              have hk0 : (nb <<< 1#64).toNat = 2 * nb.toNat := by
                                have := c.hscr; unfold dimacsBound at this
                                exact s13_bv64_shl1 nb (by omega)
                              have hk1 : ((nb <<< 1#64) + 1#64).toNat = 2 * nb.toNat + 1 := by
                                have := c.hscr; unfold dimacsBound at this
                                exact s13_bv64_shl1_add1 nb (by omega)
                              have hnb0_lt : (nb <<< 1#64).toNat <
                                  ({ s with
                                      core := { s.core with lit_mark := lm1 }
                                      scratch := { s.scratch with scratch_buf := scrP } }
                                    ).scratch.scratch_buf.length := by
                                dsimp only; omega
                              let scrNext := scrP.set (nb <<< 1#64).toNat (l.setWidth 32)
                              have hnb1_lt : ((nb <<< 1#64) + 1#64).toNat <
                                  ({ s with
                                      core := { s.core with lit_mark := lm1 }
                                      scratch := { s.scratch with
                                        scratch_buf := scrNext } }
                                    ).scratch.scratch_buf.length := by
                                dsimp only [scrNext]; rw [List.length_set]; omega
                              have hnb1_eq : (nb + 1#64).toNat = nb.toNat + 1 := by
                                have := c.hscr; unfold dimacsBound at this; bv_omega
                              have hl32_eq : (l.setWidth 32).toNat = l_lit := by
                                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hl_eq
                              have hbp1 := s13_binPairsOk_push hbpP (by omega)
                                (by rw [hl32_eq]; exact hl_lt) hot_lt
                                (by rw [hl32_eq]; exact hent_bin)
                              c0_hsteps_nogrp
                              let scrF :=
                                (scrP.set (2 * nb.toNat) (l.setWidth 32)).set (2 * nb.toNat + 1) ot
                              have hbp1' : BinPairsOk c F_cur s (nb + 1#64).toNat scrF := by
                                dsimp only [scrF]; rw [hnb1_eq]; exact hbp1
                              refine hJs5 (nb + 1#64, false, ()) _ ⟨rfl, scrF, hbp1', ?_⟩
                              dsimp only [scrF]; rw [← hk1, ← hk0]; exact (by assumption)
                            · c0_hsteps_nogrp
                              exact hJa2 nb true (p + 1#64) lm1 scrP _ hlm1_len hbpP hdirty1 hhi1
                                (by assumption)
                          · c0_hsteps_nogrp
                            exact hJs5 (nb, false, ()) _ ⟨rfl, scrP, hbpP, by assumption⟩
                        · c0_hsteps_nogrp
                          exact hJs5 (nb, false, ()) _ ⟨rfl, scrP, hbpP, by assumption⟩
                      · c0_hsteps_nogrp
                        exact hJs5 (nb, false, ()) _ ⟨rfl, scrP, hbpP, by assumption⟩)
                · c0_hsteps_nogrp
                  exact hJs4 (nb, false, ()) mP ⟨rfl, lmP, scrP, hlmP_len, hbpP, hdirtyP, hhiP, hmP⟩
              · exfalso; apply hc; dsimp only [ot] at hot_lt'
                rw [hnlits]; exact hot_lt')
        · have hnb := hc
          have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_ws) :=
            List.getElem?_eq_getElem hp_ws
          obtain ⟨hrem2, _, hslice2⟩ := s13_modeSlice_step_nonbin hslice hrem_pos hw0_eq hnb
          have hsub2 : ∀ x, S13SliceContainsBin s.core (p.toNat + 2) (rem - 2) x →
              S13SliceContainsBin s.core off.toNat sz.toNat x := fun x hx =>
            hsubP x (.step_nonbin (by omega) hw0_eq hnb hx)
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (pn, ()) m4 => pn.toNat = p.toNat + 2 ∧ m4 = mP)
            (fun _ ⟨pn, ⟨⟩⟩ m4 ⟨hpn2, hm4⟩ => by
              subst m4; c0_hsteps_nogrp
              exact hJs3 (nb, false, pn, ()) mP
                ⟨by omega, by omega, rem - 2, lmP, scrP, by omega, hpn2.symm ▸ hslice2, hlmP_len,
                  hbpP, fun x hx => hsub2 x (hpn2 ▸ hx), hdirtyP, hhiP, hmP⟩)
            (fun Js_4 hJs4 => by
              c0_hsteps_nogrp; c0_hsplit
              · have hp2_eq : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
                c0_hsteps_nogrp; exact hJs4 (p + 1#64 + 1#64, ()) mP ⟨hp2_eq, rfl⟩))
  · c0_hsteps_nogrp; exact hJa2 nb false p lmP scrP mP hlmP_len hbpP hdirtyP hhiP hmP

private def collectExpr {V : Ty → Type} {K : List Ty → Type}
    (hdr pwvec pwstk pvals plm pscr : V i64) (nlits scap_pairs : V i64)
    (contE : V i64 → Expr V K []) : Expr V K [] :=
  Expr.group (sig := [[i64, .bool, i64]]) (fun Js =>
    Blocks.cons (fun p_18 =>
      Expr.group (sig := [[]]) (fun _ =>
        Blocks.cons (fun _ =>
          Expr.jnz (Arg.var p_18.snd.fst)
            (Expr.call (as := [i64]) (bs := []) "full_sweep_bins" (Arg.var hdr, ())
              (fun _ => Expr.ret ()))
            (contE p_18.fst)) Blocks.nil)
        (fun Js_1 =>
        Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
          (Arg.var p_18.snd.snd.fst, Arg.var nlits, ())) (fun (bl, ()) =>
        Expr.jnz (Arg.var bl)
          (Expr.jnz (Arg.var p_18.snd.fst) (Expr.jump Js_1.fst ())
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1a, ()) =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var p_18.snd.snd.fst, Arg.var c1a, ()))
              (fun (l2a, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var l2a, Arg.imm 4, ())) (fun (oa, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var oa, ())) (fun (aa, ()) =>
            Expr.load i32 (Arg.var aa) (fun off32 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var off32, ())) (fun (off, ()) =>
            Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var p_18.snd.snd.fst, Arg.var c1b, ()))
              (fun (l2b, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var l2b, Arg.imm 1, ())) (fun (l2p, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var l2p, Arg.imm 4, ())) (fun (ob, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var ob, ())) (fun (ab, ()) =>
            Expr.load i32 (Arg.var ab) (fun sz32 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var sz32, ())) (fun (sz, ()) =>
            Expr.group (sig := [[i64, .bool]]) (fun _ =>
              Blocks.cons (fun st2 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p_18.snd.snd.fst, Arg.imm 1, ()))
                  (fun (ln, ()) =>
                Expr.jump Js.fst (Arg.var st2.1, Arg.var st2.2.1, Arg.var ln, ()))) Blocks.nil)
              (fun Js_2 =>
              Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var sz, Arg.imm 0, ()))
                (fun (bsz, ()) =>
              Expr.jnz (Arg.var bsz)
                (Expr.let_ (Op.mk (.add i64) (Arg.var pvals, Arg.var p_18.snd.snd.fst, ()))
                  (fun (avl, ()) =>
                Expr.load i8 (Arg.var avl) (fun lv =>
                Expr.let_ (Op.mk (.add i64) (Arg.var off, Arg.var sz, ())) (fun (end_, ()) =>
                Expr.group (sig := [[i64, .bool, i64]]) (fun _ =>
                  Blocks.cons (fun sta =>
                    clearLmExpr pwstk plm nlits off end_ sta.1 sta.2.1 Js_2.fst) Blocks.nil)
                  (fun Ja2 =>
                    scanSliceExpr pwstk pvals plm pscr nlits scap_pairs
                      p_18.snd.snd.fst off end_ p_18.fst lv p_18.snd.fst Ja2.fst)))))
                (Expr.jump Js_2.fst (Arg.var p_18.fst, Arg.var p_18.snd.fst, ())))))))))))))))))))
          (Expr.jump Js_1.fst ()))))
    Blocks.nil) (fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm false, Arg.imm 0, ()))

private theorem s13_bin_roundtrip_collect_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hSweep : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {contE : Val i64 → Expr Val Cont []}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hm : (FullMem c s ⋆ R) m)
    (hExitOv : ∀ (s1 : FullState) (m1 : Mem 64),
      s1.LengthsOk c → FullWitnessInv c F0 F_cur s1.core →
      FullLitMarksClear c s1 → FullArenaVarsNodup s1 → FullExtScratchOk c s1 →
      s1.core.cur_vars = s.core.cur_vars → s1.core.cur_level = s.core.cur_level →
      s1.core.dense_mode = s.core.dense_mode →
      s1.core.arena = s.core.arena → s1.core.arena_len = s.core.arena_len →
      s1.core.vals = s.core.vals → s1.core.lvl = s.core.lvl → s1.core.flags = s.core.flags →
      s1.core.fuel = s.core.fuel → s1.core.inconsistent = s.core.inconsistent →
      s1.core.d_cur = s.core.d_cur → s1.core.d_val = s.core.d_val →
      s1.core.frame_trail = s.core.frame_trail → s1.core.frame_dec = s.core.frame_dec →
      s1.core.trail_end = s.core.trail_end → s1.core.propagated = s.core.propagated →
      s1.core.probing = s.core.probing →
      s1.scratch.extend_len = s.scratch.extend_len →
      s1.scratch.walk_vals = s.scratch.walk_vals →
      s1.scratch.walk_best = s.scratch.walk_best →
      s1.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s1 ⋆ R) m1 → Q () m1)
    (hCont : ∀ (nb : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      s'.LengthsOk c → BinPairsOk c F_cur s nb.toNat scr' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (contE nb) m') :
    let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< 1#64
    let scap_pairs : BitVec 64 := BitVec.ofNat 64 c.scratch_cap >>> 1#64
    wp Γ Q X (collectExpr c.hdr c.pWvec c.pWstk c.pVals c.pLitMark c.pScratchBuf
      nlits scap_pairs contE) m := by
  intro nlits scap_pairs
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hwv_len : s.core.wvec.length = 4 * c.max_vars := hlen.core_ok.wvec_len
  have hmx_bd := c.hmaxv; unfold dimacsBound at hmx_bd
  have hv_len : s.core.vals.length = 2 * c.max_vars := hlen.core_ok.vals_len
  have hlm_len : s.core.lit_mark.length = 2 * c.max_vars := hlen.core_ok.lit_mark_len
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hnlits : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [s13_bv64_shl1 _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold collectExpr
  refine wp_loop_inv (ts := [i64, .bool, i64])
    (fun (nb, ov, l, ()) mL => l.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ lmL scrL, lmL.length = 2 * c.max_vars ∧
      (∀ x < 2 * c.max_vars, lmL[x]?.getD 0#8 = 0#8) ∧
      BinPairsOk c F_cur s nb.toNat scrL ∧
      (FullMem c { s with core := { s.core with lit_mark := lmL }
                          scratch := { s.scratch with scratch_buf := scrL } } ⋆ R) mL)
    (fun (_nb, _ov, l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun Js hLoop => by
      c0_hsteps_nogrp
      exact hLoop (0#64, false, 0#64, ()) m ⟨Nat.zero_le _, s.core.lit_mark, s.scratch.scratch_buf,
        hlm_len, hlm.2, ⟨hscr_len, by simp, fun _ h => by simp at h⟩, hm⟩)
    (fun Js ⟨nb, ov, l, ⟨⟩⟩ mL ⟨hl_le, lmL, scrL, hlmL, hclrL, hbpL, hmL⟩ hLoop => ?_)
  c0_hsteps_nogrp
  have hlm_eq : lmL = s.core.lit_mark := by
    refine List.ext_getElem (hlmL.trans hlm_len.symm) fun idx hi1 hi2 => ?_
    have h1 := hclrL idx (by rw [← hlmL]; exact hi1)
    have h2 := hlm.2 idx (by rw [← hlm_len]; exact hi2)
    rw [List.getElem?_eq_getElem hi1, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hi2, Option.getD_some] at h2
    exact h1.trans h2.symm
  have hmL_s : (FullMem c { s with core := { s.core with lit_mark := s.core.lit_mark },
                                    scratch := { s.scratch with scratch_buf := scrL } } ⋆ R) mL :=
    hlm_eq ▸ hmL
  let sL : FullState := { s with scratch := { s.scratch with scratch_buf := scrL } }
  have hlenL : sL.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hbpL.1 }⟩
  have hwL : FullWitnessInv c F0 F_cur sL.core := hw
  have hlmL_inv : FullLitMarksClear c sL := ⟨hlm.1, hlm.2⟩
  have hndL : FullArenaVarsNodup sL := by
    intro r hr hng; exact hnd r hr hng
  have hextL : FullExtScratchOk c sL := ⟨hext.1, hext.2⟩
  refine wp_join_group (ts := []) (fun () m1 => m1 = mL)
    (fun _ ⟨⟩ m1 hm1_eq => by
      c0_hsteps_nogrp; c0_hsplit
      · c0_hsteps_nogrp; s13a1b_call hSweep
        refine ⟨c, F0, F_cur, sL, R, rfl, hlenL, hwL, ?_, ?_⟩
        · simpa [sL, hm1_eq] using hmL_s
        · intro wvec' wstk' wlen' nb' wsort' m' s' hlen' _ _ hw' hm'
          have hlm' : FullLitMarksClear c s' := ⟨hlm.1, hlm.2⟩
          have hnd' : FullArenaVarsNodup s' := by
            intro r hr hng
            change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
            exact hndL r hr hng
          have hext' : FullExtScratchOk c s' := ⟨hextL.1, hextL.2⟩
          c0_hsteps_nogrp
          exact hExitOv s' m' hlen' hw' hlm' hnd' hext' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm'
      · exact hm1_eq ▸ hCont nb scrL mL hlenL hbpL (by simpa [sL] using hmL_s))
    (fun Js_1 hJs1 => by
      c0_hsplit_np_nobound
      · have hl_lt : l.toNat < 2 * s.core.cur_vars := by rw [← hnlits]; exact hc
        c0_hsplit_np_nobound
        · c0_hsteps_nogrp; exact hJs1 () mL rfl
        · have hovF : ov = false := by cases ov <;> simp_all
          subst hovF
          have hlay := hw.watches.layout
          have hk0 : (l <<< 1#64).toNat = 2 * l.toNat := by
            exact s13_bv64_shl1 l (by omega)
          have hk1 : ((l <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
            exact s13_bv64_shl1_add1 l (by omega)
          have h0_lt : (l <<< 1#64).toNat < sL.core.wvec.length := by dsimp only [sL]; omega
          have h1_lt : ((l <<< 1#64) + 1#64).toNat < sL.core.wvec.length := by
            dsimp only [sL]; omega
          have hoff : ((sL.core.wvec[(l <<< 1#64).toNat]'h0_lt).setWidth 64).toNat =
              fullWatchOffCore s.core l.toNat := by
            dsimp only [sL, fullWatchOffCore]
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by have := (sL.core.wvec[(l <<< 1#64).toNat]'h0_lt).isLt; omega)]
            simp only [hk0]
          have hsz : ((sL.core.wvec[((l <<< 1#64) + 1#64).toNat]'h1_lt).setWidth 64).toNat =
              fullWatchSizeCore s.core l.toNat := by
            dsimp only [sL, fullWatchSizeCore]
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt
                (by have := (sL.core.wvec[((l <<< 1#64) + 1#64).toNat]'h1_lt).isLt; omega)]
            simp only [hk1]
          have hl1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, .bool])
            (fun (nb2, _ov2, ()) m2 => ∃ lm2 scr2, lm2.length = 2 * c.max_vars ∧
              (∀ x < 2 * c.max_vars, lm2[x]?.getD 0#8 = 0#8) ∧
              BinPairsOk c F_cur s nb2.toNat scr2 ∧
              (FullMem c { s with core := { s.core with lit_mark := lm2 }
                                  scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2)
            (fun _ ⟨nb2, ov2, ⟨⟩⟩ m2 ⟨lm2, scr2, hlm2, hclr2, hbp2, hm2⟩ => by
              c0_hsteps_nogrp
              exact hLoop (nb2, ov2, l + 1#64, ()) m2 (by dsimp only; omega)
                ⟨by omega, lm2, scr2, hlm2, hclr2, hbp2, hm2⟩)
            (fun Js_2 hJs2 => by
              c0_hsteps_nogrp; c0_hsplit
              · have hl_v : l.toNat < sL.core.vals.length := by dsimp only [sL]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64, .bool, i64])
                  (fun (nbA, ovA, _pA, ()) mA => ∃ lmA scrA, lmA.length = 2 * c.max_vars ∧
                    BinPairsOk c F_cur s nbA.toNat scrA ∧
                    (∀ x < 2 * s.core.cur_vars, lmA[x]? ≠ some 0#8 →
                      S13SliceContainsBin s.core
                        ((sL.core.wvec[(l <<< 1#64).toNat]'h0_lt).setWidth 64).toNat
                        ((sL.core.wvec[((l <<< 1#64) + 1#64).toNat]'h1_lt).setWidth 64).toNat x) ∧
                    (∀ x, 2 * s.core.cur_vars ≤ x → x < 2 * c.max_vars →
                      lmA[x]?.getD 0#8 = 0#8) ∧
                    (FullMem c { s with core := { s.core with lit_mark := lmA }
                                        scratch := { s.scratch with scratch_buf := scrA } } ⋆
                      R) mA)
                  (fun _ ⟨nbA, ovA, _pA, ⟨⟩⟩ mA ⟨lmA, scrA, hlmA, hbpA, hdirtyA, hhiA, hmA⟩ => by
                    let sA : FullState :=
                      { s with scratch := { s.scratch with scratch_buf := scrA } }
                    have hlenA : ({ sA with core := { sA.core with lit_mark := lmA } } :
                        FullState).LengthsOk c :=
                      ⟨{ hlen.core_ok with lit_mark_len := hlmA },
                        { hlen.scratch_ok with scratch_buf_len := hbpA.1 }⟩
                    refine s13_bin_roundtrip_clear_lm_wp (s := sA) (lm0 := lmA) hlenA
                      hw hl_lt hoff hsz hdirtyA hhiA hmA ?_
                    intro lmF mF hlmF hclrF hmF
                    exact hJs2 (nbA, ovA, ()) mF ⟨lmF, scrA, hlmF, hclrF, hbpA, hmF⟩)
                  (fun Ja2 hJa2 =>
                    s13_bin_roundtrip_scan_slice_wp (s := s) (lm0 := lmL) (scr0 := scrL)
                      ⟨{ hlen.core_ok with lit_mark_len := hlmL },
                        { hlen.scratch_ok with scratch_buf_len := hbpL.1 }⟩
                      hw rfl hl_lt hoff hsz hclrL hbpL hmL
                      (fun nb' ov' pfin lm' scr' m' hlm' hbp' hdirty' hhi' hm' =>
                        hJa2 (nb', ov', pfin, ()) m' ⟨lm', scr', hlm', hbp', hdirty', hhi', hm'⟩))
              · c0_hsteps_nogrp; exact hJs2 (nb, false, ()) mL ⟨lmL, scrL, hlmL, hclrL, hbpL, hmL⟩)
      · c0_hsteps_nogrp; exact hJs1 () mL rfl)

private def shellShiftExpr {V : Ty → Type} {K : List Ty → Type}
    (pscr : V i64) (gap i : V i64) (pa pb : V i32) (Js_3 : K [i64]) : Expr V K [] :=
  Expr.group (sig := [[i64]]) (fun Js_j =>
    Blocks.cons (fun (j, ()) =>
      Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var j, Arg.var gap, ())) (fun (bj, ()) =>
      Expr.jnz (Arg.var bj)
        (Expr.let_ (Op.mk (.sub i64) (Arg.var j, Arg.var gap, ())) (fun (jg, ()) =>
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1a, ()) =>
        Expr.let_ (Op.mk (.shl i64) (Arg.var jg, Arg.var c1a, ())) (fun (jg2, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var jg2, Arg.imm 4, ())) (fun (og0, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var og0, ())) (fun (ag0, ()) =>
        Expr.load i32 (Arg.var ag0) (fun qa =>
        Expr.let_ (Op.mk (.sub i64) (Arg.var j, Arg.var gap, ())) (fun (jg', ()) =>
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
        Expr.let_ (Op.mk (.shl i64) (Arg.var jg', Arg.var c1b, ())) (fun (jg2b, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var jg2b, Arg.imm 1, ())) (fun (jg2p, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var jg2p, Arg.imm 4, ())) (fun (og1, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var og1, ())) (fun (ag1, ()) =>
        Expr.load i32 (Arg.var ag1) (fun qb =>
        Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var qa, Arg.var pa, ())) (fun (bq, ()) =>
        Expr.jnz (Arg.var bq)
          (Expr.jump Js_3 (Arg.var j, ()))
          (Expr.group (sig := [[]]) (fun _ =>
            Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (s1a, ()) =>
              Expr.let_ (Op.mk (.shl i64) (Arg.var j, Arg.var s1a, ())) (fun (j2a, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var j2a, Arg.imm 4, ())) (fun (oj0, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oj0, ())) (fun (aj0, ()) =>
              Expr.store (Arg.var qa) (Arg.var aj0)
                (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (s1b, ()) =>
                Expr.let_ (Op.mk (.shl i64) (Arg.var j, Arg.var s1b, ())) (fun (j2b, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var j2b, Arg.imm 1, ())) (fun (j2p, ()) =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var j2p, Arg.imm 4, ())) (fun (oj1, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oj1, ())) (fun (aj1, ()) =>
                Expr.store (Arg.var qb) (Arg.var aj1)
                  (Expr.let_ (Op.mk (.sub i64) (Arg.var j, Arg.var gap, ())) (fun (jn, ()) =>
                  Expr.jump Js_j.fst (Arg.var jn, ())))))))))))))) Blocks.nil)
            (fun Js_4 =>
              Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var qa, Arg.var pa, ()))
                (fun (beq, ()) =>
              Expr.jnz (Arg.var beq)
                (Expr.let_ (Op.mk (.cmp .ule i32 .bool rfl) (Arg.var qb, Arg.var pb, ()))
                  (fun (ble, ()) =>
                Expr.jnz (Arg.var ble) (Expr.jump Js_3 (Arg.var j, ())) (Expr.jump Js_4.fst ())))
                (Expr.jump Js_4.fst ())))))))))))))))))))
        (Expr.jump Js_3 (Arg.var j, ()))))
    Blocks.nil) (fun Js_j => Expr.jump Js_j.fst (Arg.var i, ()))

private theorem s13_bin_sort_shift_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nb gap i : BitVec 64} {pa pb : BitVec 32} {scr0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Js_3 : Cont [i64]}
    (hgap : 1 ≤ gap.toNat) (hi_lt : i.toNat < nb.toNat)
    (_hpa : pa.toNat < 2 * s.core.cur_vars) (_hpb : pb.toNat < 2 * s.core.cur_vars)
    (_hpent : (cnfOfClauses F_cur).EntailsClause (cnfClause [pa.toNat, pb.toNat]))
    (hbp0 : BinPairsOk c F_cur s nb.toNat scr0)
    (hm0 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m0)
    (hJs3 : ∀ (jfin : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      jfin.toNat < nb.toNat → BinPairsOk c F_cur s nb.toNat scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Js_3 (jfin, ()) m') :
    wp Γ Q X (shellShiftExpr c.pScratchBuf gap i pa pb Js_3) m0 := by
  unfold shellShiftExpr
  refine wp_loop_inv (ts := [i64])
    (fun (j, ()) mJ => j.toNat < nb.toNat ∧ ∃ scrJ, BinPairsOk c F_cur s nb.toNat scrJ ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scrJ } } ⋆ R) mJ)
    (fun (j, ()) _ => j.toNat)
    (fun Js_j hLoop => by c0_hsteps_nogrp; exact hLoop (i, ()) m0 ⟨hi_lt, scr0, hbp0, hm0⟩)
    (fun Js_j ⟨j, ⟨⟩⟩ mJ ⟨hj_lt, scrJ, hbpJ, hmJ⟩ hLoop => ?_)
  c0_hsplit
  · have hjg : gap.toNat ≤ j.toNat := hc
    have hjg_lt : (j - gap).toNat < nb.toNat := by bv_omega
    have hnb_bd : 2 * nb.toNat ≤ c.scratch_cap := hbpJ.2.1
    have hsc_len : scrJ.length = c.scratch_cap := hbpJ.1
    have hjg0 : ((j - gap) <<< 1#64).toNat = 2 * (j - gap).toNat := by
      have := c.hscr; unfold dimacsBound at this; exact s13_bv64_shl1 _ (by omega)
    have hjg1 : (((j - gap) <<< 1#64) + 1#64).toNat = 2 * (j - gap).toNat + 1 := by
      have := c.hscr; unfold dimacsBound at this; exact s13_bv64_shl1_add1 _ (by omega)
    have hqa_lt : ((j - gap) <<< 1#64).toNat <
        ({ s with scratch := { s.scratch with scratch_buf := scrJ } }
          ).scratch.scratch_buf.length := by
      dsimp only; omega
    have hqb_lt : (((j - gap) <<< 1#64) + 1#64).toNat <
        ({ s with scratch := { s.scratch with scratch_buf := scrJ } }
          ).scratch.scratch_buf.length := by
      dsimp only; omega
    obtain ⟨hqa_v, hqb_v, hqent⟩ := hbpJ.2.2 (j - gap).toNat hjg_lt
    have hqa_eq : scrJ[((j - gap) <<< 1#64).toNat]'hqa_lt =
        scrJ[2 * (j - gap).toNat]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem (by rw [hjg0] at hqa_lt; exact hqa_lt), Option.getD_some]
      simp only [hjg0]
    have hqb_eq : scrJ[(((j - gap) <<< 1#64) + 1#64).toNat]'hqb_lt =
        scrJ[2 * (j - gap).toNat + 1]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem (by rw [hjg1] at hqb_lt; exact hqb_lt), Option.getD_some]
      simp only [hjg1]
    c0_hsteps_nogrp; c0_hsplit
    · c0_hsteps_nogrp; exact hJs3 j scrJ mJ hj_lt hbpJ hmJ
    · refine wp_join_group (ts := []) (fun () m => m = mJ)
        (by rintro _ ⟨⟩ _ rfl
            have hj0 : (j <<< 1#64).toNat = 2 * j.toNat := by
              have := c.hscr; unfold dimacsBound at this; exact s13_bv64_shl1 j (by omega)
            have hj1 : ((j <<< 1#64) + 1#64).toNat = 2 * j.toNat + 1 := by
              have := c.hscr; unfold dimacsBound at this; exact s13_bv64_shl1_add1 j (by omega)
            have hj0_lt : (j <<< 1#64).toNat <
                ({ s with scratch := { s.scratch with scratch_buf := scrJ } }
                  ).scratch.scratch_buf.length := by
              dsimp only; omega
            let scrNext := scrJ.set (j <<< 1#64).toNat (scrJ[((j - gap) <<< 1#64).toNat]'hqa_lt)
            have hj1_lt : ((j <<< 1#64) + 1#64).toNat <
                ({ s with scratch := { s.scratch with
                  scratch_buf := scrNext } }).scratch.scratch_buf.length := by
              dsimp only [scrNext]; rw [List.length_set]; omega
            have hbpJ' := s13_binPairsOk_set hbpJ hj_lt hqa_v hqb_v hqent
            c0_hsteps_nogrp
            let scrF := (scrJ.set (2 * j.toNat) (scrJ[2 * (j - gap).toNat]?.getD 0#32)).set
              (2 * j.toNat + 1) (scrJ[2 * (j - gap).toNat + 1]?.getD 0#32)
            refine hLoop (j - gap, ()) _ (by dsimp only; bv_omega) ⟨hjg_lt, scrF, hbpJ', ?_⟩
            dsimp only [scrF]; rw [← hj1, ← hj0, ← hqa_eq, ← hqb_eq]; exact (by assumption))
        (fun Js_4 hJs4 => by
          c0_hsplit_np_nobound
          · c0_hsplit_np_nobound
            · c0_hsteps_nogrp; exact hJs3 j scrJ mJ hj_lt hbpJ hmJ
            · c0_hsteps_nogrp; exact hJs4 () mJ rfl
          · c0_hsteps_nogrp; exact hJs4 () mJ rfl)
  · c0_hsteps_nogrp; exact hJs3 j scrJ mJ hj_lt hbpJ hmJ

private def shellSortExpr {V : Ty → Type} {K : List Ty → Type}
    (pscr : V i64) (nb : V i64) (Js_out : K []) : Expr V K [] :=
  Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var nb, Arg.imm 1, ())) (fun (bg1, ()) =>
  Expr.jnz (Arg.var bg1)
    (Expr.let_ (Op.mk (.udiv 64) (Arg.var nb, Arg.imm 3, ())) (fun (lim, ()) =>
    Expr.group (sig := [[i64]]) (fun Js_1 =>
      Blocks.cons (fun (gap0, ()) =>
        Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var gap0, Arg.var lim, ()))
          (fun (blim, ()) =>
        Expr.jnz (Arg.var blim)
          (Expr.let_ (Op.mk (.mul i64) (Arg.var gap0, Arg.imm 3, ())) (fun (g3, ()) =>
          Expr.let_ (Op.mk (.add i64) (Arg.var g3, Arg.imm 1, ())) (fun (gn, ()) =>
          Expr.jump Js_1.fst (Arg.var gn, ()))))
          (Expr.group (sig := [[i64]]) (fun Js_2 =>
            Blocks.cons (fun (gap, ()) =>
              Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var gap, Arg.imm 1, ()))
                (fun (bge1, ()) =>
              Expr.jnz (Arg.var bge1)
                (Expr.group (sig := [[i64]]) (fun Js_i =>
                  Blocks.cons (fun (i, ()) =>
                    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var i, Arg.var nb, ()))
                      (fun (bi, ()) =>
                    Expr.jnz (Arg.var bi)
                      (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1a, ()) =>
                      Expr.let_ (Op.mk (.shl i64) (Arg.var i, Arg.var c1a, ())) (fun (i2a, ()) =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var i2a, Arg.imm 4, ())) (fun (oi0, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oi0, ()))
                        (fun (ai0, ()) =>
                      Expr.load i32 (Arg.var ai0) (fun pa =>
                      Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
                      Expr.let_ (Op.mk (.shl i64) (Arg.var i, Arg.var c1b, ())) (fun (i2b, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var i2b, Arg.imm 1, ())) (fun (i2p, ()) =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var i2p, Arg.imm 4, ())) (fun (oi1, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oi1, ()))
                        (fun (ai1, ()) =>
                      Expr.load i32 (Arg.var ai1) (fun pb =>
                      Expr.group (sig := [[i64]]) (fun _ =>
                        Blocks.cons (fun (jfin, ()) =>
                          Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (s1a, ()) =>
                          Expr.let_ (Op.mk (.shl i64) (Arg.var jfin, Arg.var s1a, ()))
                            (fun (jf2a, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var jf2a, Arg.imm 4, ()))
                            (fun (oj0, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oj0, ()))
                            (fun (aj0, ()) =>
                          Expr.store (Arg.var pa) (Arg.var aj0)
                            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (s1b, ()) =>
                            Expr.let_ (Op.mk (.shl i64) (Arg.var jfin, Arg.var s1b, ()))
                              (fun (jf2b, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var jf2b, Arg.imm 1, ()))
                              (fun (jf2p, ()) =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var jf2p, Arg.imm 4, ()))
                              (fun (oj1, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var pscr, Arg.var oj1, ()))
                              (fun (aj1, ()) =>
                            Expr.store (Arg.var pb) (Arg.var aj1)
                              (Expr.let_ (Op.mk (.add i64) (Arg.var i, Arg.imm 1, ()))
                                (fun (inext, ()) =>
                              Expr.jump Js_i.fst (Arg.var inext, ())))))))))))))) Blocks.nil)
                        (fun Js_3 => shellShiftExpr pscr gap i pa pb Js_3.fst)))))))))))))
                      (Expr.let_ (Op.mk (.udiv 64) (Arg.var gap, Arg.imm 3, ())) (fun (gd, ()) =>
                      Expr.jump Js_2.fst (Arg.var gd, ())))))
                  Blocks.nil) (fun Js_i => Expr.jump Js_i.fst (Arg.var gap, ())))
                (Expr.jump Js_out ()))) Blocks.nil)
            (fun Js_2 => Expr.jump Js_2.fst (Arg.var gap0, ()))))) Blocks.nil)
      (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 1, ()))))
    (Expr.jump Js_out ()))

private theorem s13_bin_sort_shell_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nb : BitVec 64} {scr0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Js_out : Cont []}
    (hbp0 : BinPairsOk c F_cur s nb.toNat scr0)
    (hm0 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m0)
    (hOut : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      BinPairsOk c F_cur s nb.toNat scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Js_out () m') :
    wp Γ Q X (shellSortExpr c.pScratchBuf nb Js_out) m0 := by
  have hnb_bd := hbp0.2.1
  have hscr_bd := c.hscr; unfold dimacsBound at hscr_bd
  unfold shellSortExpr
  c0_hsteps_nogrp; c0_hsplit
  · have hnb_gt1 : 1 < nb.toNat := hc
    have hlim_lt : (nb / 3#64).toNat < nb.toNat := by
      rw [BitVec.toNat_udiv]; exact Nat.div_lt_self (by omega) (by decide)
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (gap0, ()) mG => 1 ≤ gap0.toNat ∧ gap0.toNat < 3 * nb.toNat ∧ mG = m0)
      (fun (gap0, ()) _ => 3 * nb.toNat - gap0.toNat)
      (fun Js_1 hLoop1 => by
        c0_hsteps_nogrp; exact hLoop1 (1#64, ()) m0
          ⟨le_refl 1, by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, rfl⟩)
      (fun Js_1 ⟨gap0, ⟨⟩⟩ mG ⟨hgap1, hgap_bd, hmG⟩ hLoop1 => ?_)
    subst mG
    c0_hsplit
    · have hglim : gap0.toNat < (nb / 3#64).toNat := hc
      rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl] at hglim
      have hgn : (gap0 * 3#64 + 1#64).toNat = 3 * gap0.toNat + 1 := by bv_omega
      have hinc : gap0.toNat < 3 * gap0.toNat + 1 := by omega
      c0_hsteps_nogrp
      exact hLoop1 (gap0 * 3#64 + 1#64, ()) m0 (by dsimp only; rw [hgn]; omega)
        ⟨by omega, by rw [hgn]; omega, rfl⟩
    · c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (gap, ()) m2 => gap.toNat < 3 * nb.toNat ∧ ∃ scr2, BinPairsOk c F_cur s nb.toNat scr2 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2)
        (fun (gap, ()) _ => gap.toNat)
        (fun Js_2 hLoop2 => by
          c0_hsteps_nogrp; exact hLoop2 (gap0, ()) m0 ⟨hgap_bd, scr0, hbp0, hm0⟩)
        (fun Js_2 ⟨gap, ⟨⟩⟩ m2 ⟨hgap_lt, scr2, hbp2, hm2⟩ hLoop2 => ?_)
      c0_hsplit
      · have hgap_ge1 : 1 ≤ gap.toNat := hc
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (i, ()) mI => gap.toNat ≤ i.toNat ∧ ∃ scrI, BinPairsOk c F_cur s nb.toNat scrI ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scrI } } ⋆ R) mI)
          (fun (i, ()) _ => nb.toNat - i.toNat)
          (fun Js_i hLoopI => by
            c0_hsteps_nogrp; exact hLoopI (gap, ()) m2 ⟨le_refl _, scr2, hbp2, hm2⟩)
          (fun Js_i ⟨i, ⟨⟩⟩ mI ⟨hgi, scrI, hbpI, hmI⟩ hLoopI => ?_)
        c0_hsplit
        · have hi_lt : i.toNat < nb.toNat := hc
          have hsc_len : scrI.length = c.scratch_cap := hbpI.1
          have hnb_bdI : 2 * nb.toNat ≤ c.scratch_cap := hbpI.2.1
          have hi0 : (i <<< 1#64).toNat = 2 * i.toNat := s13_bv64_shl1 i (by omega)
          have hi1 : ((i <<< 1#64) + 1#64).toNat = 2 * i.toNat + 1 :=
            s13_bv64_shl1_add1 i (by omega)
          have hpa_lt : (i <<< 1#64).toNat <
              ({ s with scratch := { s.scratch with
                scratch_buf := scrI } }).scratch.scratch_buf.length := by dsimp only; omega
          have hpb_lt : ((i <<< 1#64) + 1#64).toNat <
              ({ s with scratch := { s.scratch with
                scratch_buf := scrI } }).scratch.scratch_buf.length := by dsimp only; omega
          obtain ⟨hpa_v, hpb_v, hpent⟩ := hbpI.2.2 i.toNat hi_lt
          have hpa_eq : scrI[(i <<< 1#64).toNat]'hpa_lt = scrI[2 * i.toNat]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by rw [hi0] at hpa_lt; exact hpa_lt), Option.getD_some]
            simp only [hi0]
          have hpb_eq : scrI[((i <<< 1#64) + 1#64).toNat]'hpb_lt =
              scrI[2 * i.toNat + 1]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by rw [hi1] at hpb_lt; exact hpb_lt), Option.getD_some]
            simp only [hi1]
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (jfin, ()) mJ => jfin.toNat < nb.toNat ∧
              ∃ scrJ, BinPairsOk c F_cur s nb.toNat scrJ ∧
              (FullMem c { s with scratch := { s.scratch with scratch_buf := scrJ } } ⋆ R) mJ)
            (fun _ ⟨jfin, ⟨⟩⟩ mJ' ⟨hjf_lt, scrJ, hbpJ, hmJ⟩ => by
              have hscJ_len : scrJ.length = c.scratch_cap := hbpJ.1
              have hnb_bdJ : 2 * nb.toNat ≤ c.scratch_cap := hbpJ.2.1
              have hj0 : (jfin <<< 1#64).toNat = 2 * jfin.toNat := s13_bv64_shl1 jfin (by omega)
              have hj1 : ((jfin <<< 1#64) + 1#64).toNat = 2 * jfin.toNat + 1 :=
                s13_bv64_shl1_add1 jfin (by omega)
              have hj0_lt : (jfin <<< 1#64).toNat <
                  ({ s with scratch := { s.scratch with
                    scratch_buf := scrJ } }).scratch.scratch_buf.length := by dsimp only; omega
              let scrNext := scrJ.set (jfin <<< 1#64).toNat (scrI[(i <<< 1#64).toNat]'hpa_lt)
              have hj1_lt : ((jfin <<< 1#64) + 1#64).toNat <
                  ({ s with scratch := { s.scratch with
                    scratch_buf := scrNext } }).scratch.scratch_buf.length := by
                dsimp only [scrNext]; rw [List.length_set]; omega
              have hbpJ' := s13_binPairsOk_set hbpJ hjf_lt hpa_v hpb_v hpent
              have hi_next : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
              c0_hsteps_nogrp
              let scrF := (scrJ.set (2 * jfin.toNat) (scrI[2 * i.toNat]?.getD 0#32)).set
                (2 * jfin.toNat + 1) (scrI[2 * i.toNat + 1]?.getD 0#32)
              refine hLoopI (i + 1#64, ()) _ (by dsimp only; omega) ⟨by omega, _, hbpJ', ?_⟩
              dsimp only [scrF]; rw [← hj1, ← hj0, ← hpa_eq, ← hpb_eq]; exact (by assumption))
            (fun Js_3 hJs3 =>
              s13_bin_sort_shift_wp hgap_ge1 hi_lt
                (by dsimp only; change (scrI[(i <<< 1#64).toNat]'hpa_lt).toNat < 2 * s.core.cur_vars
                    rw [hpa_eq]; exact hpa_v)
                (by dsimp only; change (scrI[((i <<< 1#64) + 1#64).toNat]'hpb_lt).toNat <
                      2 * s.core.cur_vars
                    rw [hpb_eq]; exact hpb_v)
                (by dsimp only
                    change (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [(scrI[(i <<< 1#64).toNat]'hpa_lt).toNat,
                                  (scrI[((i <<< 1#64) + 1#64).toNat]'hpb_lt).toNat])
                    rw [hpa_eq, hpb_eq]; exact hpent) hbpI hmI
                (fun jfin scrJ mJ hjf hbpJ hmJ => hJs3 (jfin, ()) mJ ⟨hjf, scrJ, hbpJ, hmJ⟩))
        · have hdiv_lt : (gap / 3#64).toNat < gap.toNat := by
            rw [BitVec.toNat_udiv]; exact Nat.div_lt_self hgap_ge1 (by decide)
          c0_hsteps_nogrp
          exact hLoop2 (gap / 3#64, ()) mI hdiv_lt ⟨by omega, scrI, hbpI, hmI⟩
      · c0_hsteps_nogrp; exact hOut scr2 m2 hbp2 hm2
  · c0_hsteps_nogrp; exact hOut scr0 m0 hbp0 hm0

private def s13EmitExpr (c : FullCfg) (nlits nb : Val i64) : Expr Val Cont [] :=
  Expr.group (sig := [[i64]]) (fun Js =>
    Blocks.cons (fun (l, ()) =>
      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var l, Arg.var nlits, ()))
        (fun (bl, ()) =>
      Expr.jnz (Arg.var bl)
        (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
        Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1, ())) (fun (l2, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var l2, Arg.imm 4, ())) (fun (o0, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pWvec, Arg.var o0, ())) (fun (a0, ()) =>
        Expr.store (t := i32) (Arg.imm 0) (Arg.var a0)
          (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
          Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1b, ())) (fun (l2b, ()) =>
          Expr.let_ (Op.mk (.add i64) (Arg.var l2b, Arg.imm 1, ())) (fun (l2p, ()) =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var l2p, Arg.imm 4, ())) (fun (o1, ()) =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pWvec, Arg.var o1, ())) (fun (a1, ()) =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var a1)
            (Expr.let_ (Op.mk (.add i64) (Arg.var l, Arg.imm 1, ())) (fun (ln, ()) =>
            Expr.jump Js.fst (Arg.var ln, ()))))))))))))))
        (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) (fun (z0, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var z0, Arg.imm 4, ())) (fun (oz, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pWstk, Arg.var oz, ())) (fun (az, ()) =>
        Expr.store (t := i32) (Arg.imm 0) (Arg.var az)
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) (fun (pwl, ()) =>
          Expr.store (t := i64) (Arg.imm 1) (Arg.var pwl)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) (fun (pwu, ()) =>
            Expr.store (t := i64) (Arg.imm 0) (Arg.var pwu)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ()))
                (fun (pnb, ()) =>
              Expr.store (Arg.var nb) (Arg.var pnb)
                (Expr.group (sig := [[i64]]) (fun Jk =>
                  Blocks.cons (fun (k, ()) =>
                    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var k, Arg.var nb, ()))
                      (fun (bk, ()) =>
                    Expr.jnz (Arg.var bk)
                      (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
                      Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1, ())) (fun (k2, ()) =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var k2, Arg.imm 4, ())) (fun (ok0, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pScratchBuf, Arg.var ok0, ()))
                        (fun (ak0, ()) =>
                      Expr.load i32 (Arg.var ak0) (fun a =>
                      Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
                      Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1b, ())) (fun (k2b, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var k2b, Arg.imm 1, ())) (fun (k2p, ()) =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var k2p, Arg.imm 4, ())) (fun (ok1, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pScratchBuf, Arg.var ok1, ()))
                        (fun (ak1, ()) =>
                      Expr.load i32 (Arg.var ak1) (fun b =>
                      Expr.let_ (Op.mk (.and i32) (Arg.var b, Arg.imm 0x7FFFFFFF, ()))
                        (fun (bm, ()) =>
                      Expr.let_ (Op.mk (.or i32) (Arg.var bm, Arg.imm 0x80000000, ()))
                        (fun (wb, ()) =>
                      Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                        "full_watch_push"
                        (Arg.var c.hdr, Arg.var a, Arg.var wb, Arg.imm 0, Arg.imm 1, ())
                        (fun (_, ()) =>
                      Expr.let_ (Op.mk (.and i32) (Arg.var a, Arg.imm 0x7FFFFFFF, ()))
                        (fun (am, ()) =>
                      Expr.let_ (Op.mk (.or i32) (Arg.var am, Arg.imm 0x80000000, ()))
                        (fun (wa, ()) =>
                      Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                        "full_watch_push"
                        (Arg.var c.hdr, Arg.var b, Arg.var wa, Arg.imm 0, Arg.imm 1, ())
                        (fun (_, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var k, Arg.imm 1, ())) (fun (kn, ()) =>
                      Expr.jump Jk.fst (Arg.var kn, ()))))))))))))))))))))
                      (Expr.ret ())))
                  Blocks.nil) (fun Jk => Expr.jump Jk.fst (Arg.imm 0, ())))))))))))))))
    Blocks.nil) (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

private theorem s13_arenaPermEq_of_eq {k k' : FullCoreState}
    (har : k'.arena = k.arena) (hal : k'.arena_len = k.arena_len) : FullArenaPermEq k k' :=
  ⟨hal, by unfold fullArenaClauseRefsCore; rw [har, hal], fun _ _ =>
    ⟨by simp only [fullArenaClauseSizeCore, har],
     by simp only [fullArenaClauseGarbCore, fullArenaHdrCore, har],
     by simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har]
        exact List.Perm.refl _⟩⟩

/-- Step-13 `full_dense_bin_roundtrip_fid` satisfies `step13DenseBinRoundtripSpec`. -/
theorem full_dense_bin_roundtrip_fid_s13_wp (Γ : Env)
    (hFlushLarge : ∀ a m Q X, step13FwdFlushLargeCoreSpec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, step13DenseBinRoundtripSpec a m Q X →
      Func.wp Γ full_dense_bin_roundtrip_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, hQ⟩
  unfold Func.wp full_dense_bin_roundtrip_fid_body
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps_nogrp
    exact hQ s m hlen hw hlm hnd hext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl (s13_arenaPermEq_of_eq rfl rfl) rfl rfl rfl rfl hm
  · c0_hsteps_nogrp; s13a1b_call hFlushLarge
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, ?_⟩
    intro s1 m1 hlen1 hw1 hlm1 hnd1 hext1 hcv1 hcl1 hdm1 har1 hal1 hval1 hlvl1 hfl1 hfu1
      _hoom1 hinc1 hdc1 hdv1 _hnb1 hft1 hfd1 hte1 hpr1 hprb1 hll1 hex1 hwv1 hwb1 _ _ _ _ _ _ _ hm1
    have hret1 : ∀ s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_vars = s1.core.cur_vars → s'.core.cur_level = s1.core.cur_level →
        s'.core.dense_mode = s1.core.dense_mode →
        s'.core.arena = s1.core.arena → s'.core.arena_len = s1.core.arena_len →
        s'.core.vals = s1.core.vals → s'.core.lvl = s1.core.lvl →
        s'.core.flags = s1.core.flags → s'.core.fuel = s1.core.fuel →
        s'.core.inconsistent = s1.core.inconsistent → s'.core.d_cur = s1.core.d_cur →
        s'.core.d_val = s1.core.d_val → s'.core.frame_trail = s1.core.frame_trail →
        s'.core.frame_dec = s1.core.frame_dec → s'.core.trail_end = s1.core.trail_end →
        s'.core.propagated = s1.core.propagated →
        s'.scratch.extend_len = s1.scratch.extend_len →
        s'.scratch.walk_vals = s1.scratch.walk_vals →
        s'.scratch.walk_best = s1.scratch.walk_best →
        s'.scratch.last_learned = s1.scratch.last_learned →
        s'.core.probing = s1.core.probing →
        (FullMem c s' ⋆ R) m' → Q () m' := by
      intro s' m' a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
        c1 c2 c3 c4 b17 hm'
      exact hQ s' m' a1 a2 a3 a4 a5 (b1.trans hcv1) (b2.trans hcl1) (b3.trans hdm1)
        (b4.trans har1) (b5.trans hal1) (b6.trans hval1) (b7.trans hlvl1) (b8.trans hfl1)
        (b9.trans hfu1) (b10.trans hinc1) (b11.trans hdc1) (b12.trans hdv1)
        (b13.trans hft1) (b14.trans hfd1) (b15.trans hte1) (b16.trans hpr1)
        (b17.trans hprb1) (s13_arenaPermEq_of_eq (b4.trans har1) (b5.trans hal1))
        (c1.trans hex1) (c2.trans hwv1) (c3.trans hwb1) (c4.trans hll1) hm'
    c0_hsplit_np_nobound
    · c0_hsteps_nogrp
      exact hret1 s1 m1 hlen1 hw1 hlm1 hnd1 hext1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl hm1
    · c0_hsplit_np_nobound
      · c0_hsteps_nogrp
        exact hret1 s1 m1 hlen1 hw1 hlm1 hnd1 hext1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl hm1
      · have hwcap : 0 < c.wcap := by
          have := Nat.eq_zero_or_pos c.wcap
          rcases this with hz | hpos
          · exfalso; apply hc; rw [hz]; rfl
          · exact hpos
        have hcv_bd : 2 * s1.core.cur_vars < 2 ^ 30 := by
          have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
        c0_hsteps_nogrp
        simp only [show BitVec.ofNat 64 s.core.cur_vars = BitVec.ofNat 64 s1.core.cur_vars
          from by rw [hcv1]]
        refine s13_bin_roundtrip_collect_wp (X := X)
          (contE := s13EmitExpr c (BitVec.ofNat 64 s1.core.cur_vars <<< 1#64))
          hSweepBins hlen1 hw1 hlm1 hnd1 hext1 hm1
          (fun sE mE a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              b17 c1 c2 c3 c4 hmE =>
            hret1 sE mE a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              c1 c2 c3 c4 b17 hmE)
          ?_
        intro nb scr' m' _ hlen' hbp' hm'
        have hlm' : FullLitMarksClear c { s1 with scratch :=
            { s1.scratch with scratch_buf := scr' } } := ⟨hlm1.1, hlm1.2⟩
        have hnd' : FullArenaVarsNodup { s1 with scratch :=
            { s1.scratch with scratch_buf := scr' } } := by
          simpa [FullArenaVarsNodup, fullArenaClauseRefs, fullArenaClauseRefsCore,
            fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaClauseLits,
            fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hnd1
        have hext' : FullExtScratchOk c { s1 with scratch :=
            { s1.scratch with scratch_buf := scr' } } :=
          FullExtScratchOk.of_pres hext1 ⟨rfl, rfl⟩ fun r hr => hr
        exact s13_bin_roundtrip_emit_wp
          (s := { s1 with scratch := { s1.scratch with scratch_buf := scr' } })
          hPush hlen' hw1 hlm' hnd' hext' hwcap hcv_bd
          ⟨hbp'.1, hbp'.2.1, hbp'.2.2⟩ hm'
          (fun sF mF a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              b17 c1 c2 c3 c4 hmF =>
            hret1 sF mF a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              c1 c2 c3 c4 b17 hmF)

/-- Step-13 `full_dense_bin_sort_roundtrip_fid` satisfies
`step13DenseBinSortRoundtripSpec`. -/
theorem full_dense_bin_sort_roundtrip_fid_s13_wp (Γ : Env)
    (hFlushLarge : ∀ a m Q X, step13FwdFlushLargeCoreSpec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, Full.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, step13DenseBinSortRoundtripSpec a m Q X →
      Func.wp Γ full_dense_bin_sort_roundtrip_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, hQ⟩
  unfold Func.wp full_dense_bin_sort_roundtrip_fid_body
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps_nogrp
    exact hQ s m hlen hw hlm hnd hext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl (s13_arenaPermEq_of_eq rfl rfl) rfl rfl rfl rfl hm
  · c0_hsteps_nogrp; s13a1b_call hFlushLarge
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, ?_⟩
    intro s1 m1 hlen1 hw1 hlm1 hnd1 hext1 hcv1 hcl1 hdm1 har1 hal1 hval1 hlvl1 hfl1 hfu1
      _hoom1 hinc1 hdc1 hdv1 _hnb1 hft1 hfd1 hte1 hpr1 hprb1 hll1 hex1 hwv1 hwb1 _ _ _ _ _ _ _ hm1
    have hret1 : ∀ s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_vars = s1.core.cur_vars → s'.core.cur_level = s1.core.cur_level →
        s'.core.dense_mode = s1.core.dense_mode →
        s'.core.arena = s1.core.arena → s'.core.arena_len = s1.core.arena_len →
        s'.core.vals = s1.core.vals → s'.core.lvl = s1.core.lvl →
        s'.core.flags = s1.core.flags → s'.core.fuel = s1.core.fuel →
        s'.core.inconsistent = s1.core.inconsistent → s'.core.d_cur = s1.core.d_cur →
        s'.core.d_val = s1.core.d_val → s'.core.frame_trail = s1.core.frame_trail →
        s'.core.frame_dec = s1.core.frame_dec → s'.core.trail_end = s1.core.trail_end →
        s'.core.propagated = s1.core.propagated →
        s'.scratch.extend_len = s1.scratch.extend_len →
        s'.scratch.walk_vals = s1.scratch.walk_vals →
        s'.scratch.walk_best = s1.scratch.walk_best →
        s'.scratch.last_learned = s1.scratch.last_learned →
        s'.core.probing = s1.core.probing →
        (FullMem c s' ⋆ R) m' → Q () m' := by
      intro s' m' a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
        c1 c2 c3 c4 b17 hm'
      exact hQ s' m' a1 a2 a3 a4 a5 (b1.trans hcv1) (b2.trans hcl1) (b3.trans hdm1)
        (b4.trans har1) (b5.trans hal1) (b6.trans hval1) (b7.trans hlvl1) (b8.trans hfl1)
        (b9.trans hfu1) (b10.trans hinc1) (b11.trans hdc1) (b12.trans hdv1)
        (b13.trans hft1) (b14.trans hfd1) (b15.trans hte1) (b16.trans hpr1)
        (b17.trans hprb1) (s13_arenaPermEq_of_eq (b4.trans har1) (b5.trans hal1))
        (c1.trans hex1) (c2.trans hwv1) (c3.trans hwb1) (c4.trans hll1) hm'
    c0_hsplit_np_nobound
    · c0_hsteps_nogrp
      exact hret1 s1 m1 hlen1 hw1 hlm1 hnd1 hext1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl hm1
    · c0_hsplit_np_nobound
      · c0_hsteps_nogrp
        exact hret1 s1 m1 hlen1 hw1 hlm1 hnd1 hext1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl hm1
      · have hwcap : 0 < c.wcap := by
          have := Nat.eq_zero_or_pos c.wcap
          rcases this with hz | hpos
          · exfalso; apply hc; rw [hz]; rfl
          · exact hpos
        have hcv_bd : 2 * s1.core.cur_vars < 2 ^ 30 := by
          have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
        c0_hsteps_nogrp
        simp only [show BitVec.ofNat 64 s.core.cur_vars = BitVec.ofNat 64 s1.core.cur_vars
          from by rw [hcv1]]
        refine s13_bin_roundtrip_collect_wp (X := X)
          (contE := fun nb => Expr.group (sig := [[]])
            (fun Js => Blocks.cons
              (fun _ => s13EmitExpr c (BitVec.ofNat 64 s1.core.cur_vars <<< 1#64) nb)
              Blocks.nil)
            (fun Js => shellSortExpr c.pScratchBuf nb Js.fst))
          hSweepBins hlen1 hw1 hlm1 hnd1 hext1 hm1
          (fun sE mE a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              b17 c1 c2 c3 c4 hmE =>
            hret1 sE mE a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
              c1 c2 c3 c4 b17 hmE)
          ?_
        intro nb scr' m' _ _hlen' hbp' hm'
        refine wp_join_group (ts := [])
          (fun () mS => ∃ scrS, BinPairsOk c F_cur s1 nb.toNat scrS ∧
            (FullMem c { s1 with scratch := { s1.scratch with scratch_buf := scrS } } ⋆ R) mS)
          (fun _ ⟨⟩ mS ⟨scrS, hbpS, hmS⟩ => by
            let sS : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scrS } }
            have hlenS : sS.LengthsOk c :=
              ⟨hlen1.core_ok, { hlen1.scratch_ok with scratch_buf_len := hbpS.1 }⟩
            have hlmS : FullLitMarksClear c sS := ⟨hlm1.1, hlm1.2⟩
            have hndS : FullArenaVarsNodup sS := by
              simpa [sS, FullArenaVarsNodup, fullArenaClauseRefs, fullArenaClauseRefsCore,
                fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaClauseLits,
                fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hnd1
            have hextS : FullExtScratchOk c sS :=
              FullExtScratchOk.of_pres hext1 ⟨rfl, rfl⟩ fun r hr => hr
            exact s13_bin_roundtrip_emit_wp (s := sS)
              hPush hlenS hw1 hlmS hndS hextS hwcap hcv_bd hbpS hmS
              (fun sF mF a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
                  b17 c1 c2 c3 c4 hmF =>
                hret1 sF mF a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
                  c1 c2 c3 c4 b17 hmF))
          (fun Js hJs =>
            s13_bin_sort_shell_wp hbp' hm' fun scrS mS hbpS hmS =>
              hJs () mS ⟨scrS, hbpS, hmS⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1