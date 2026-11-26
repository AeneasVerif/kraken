/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofWatch0
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 8 Watch-Push WP Proofs (`FullFidelityStep8ProofWatch1`)

Parametric `(Γ : Env)` WP proofs (`0` `import all`, `public section`) for:
1. `full_watch_push_slow_m6_step8_wp`: Step-8 `fidStep8WatchPushSlowM6Fn` (`75%` proactive
   defrag guard `wusable * 4 >= wlen * 3`) against canonical `Full.fullWatchPushSpec`.
2. `full_watch_push_m6_step8_wp`: Step-8 `fidStep8WatchPushM6Fn` (`75%` fast-path skip
   `wusable * 4 < wlen * 3`) against canonical `Full.fullWatchPushSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics FullAssignAddSpecs

/-! ## 1. Case D, Case A & Cold Fallback `full_watch_push_slow_m6_step8_wp` -/

private abbrev wpushCaseDExpr (h pWvec pWstk wcap off sz cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[i64]]) (fun _JsD1 => Blocks.cons (fun (p_28 : Tup Val [i64]) =>
    Expr.group (sig := [[i64]]) (fun _JsD2 => Blocks.cons (fun (p_29 : Tup Val [i64]) =>
      Expr.group (sig := [[i64, i64, i64]]) (fun _JsD3 => Blocks.cons
        (fun (p_30 : Tup Val [i64, i64, i64]) =>
          wpushRelocExpr h pWvec pWstk p_30.fst p_30.snd.fst p_30.snd.snd.fst cVal lit w0 w1 cnt)
        Blocks.nil) fun Js =>
      eHdrLd h 56 fun ld_5 =>
      Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld_5)) fun p_31 =>
      Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_29.fst) (Arg.var p_31.fst)) fun p_32 =>
      Expr.jnz (Arg.var p_32.fst)
        (Expr.group (sig := [[i64, i64]]) (fun _Js_1 => Blocks.cons
          (fun (p_33 : Tup Val [i64, i64]) =>
          Expr.group (sig := [[i64]]) (fun _Js_2 => Blocks.cons (fun (p_34 : Tup Val [i64]) =>
            eHdrLd h 56 fun ld1 =>
            Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld1)) fun p2 =>
            Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_34.fst) (Arg.var p2.fst))
              fun p3 =>
            Expr.jnz (Arg.var p3.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.jump Js.fst (Arg.var p_33.fst, Arg.var p_33.snd.fst, Arg.var p_34.fst, ())))
            Blocks.nil) fun JsN =>
          eHdrLd h 56 fun ld1 =>
          Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld1)) fun p2 =>
          Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_29.fst) (Arg.var p2.fst)) fun p3 =>
          Expr.jnz (Arg.var p3.fst)
            (Expr.let_ (wpOp2 (.add i64) (Arg.var p_33.snd.fst) (Arg.var cVal)) fun p4 =>
             Expr.jump JsN.fst (Arg.var p4.fst, ()))
            (Expr.jump JsN.fst (Arg.var p_29.fst, ()))) Blocks.nil) fun JsE =>
         eHdrLd h 464 fun ld_6 =>
         Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var ld_6) (Arg.imm 0)) fun p_34 =>
         Expr.jnz (Arg.var p_34.fst)
           (Expr.call (as := [i64]) (bs := []) "full_wstack_defrag_m6" (Arg.var h, ()) fun _ =>
            eLit2Addr pWvec lit fun p_40 =>
            Expr.load i32 (Arg.var p_40) fun ld_7 =>
            Expr.let_ (wpOp1 (.zext 32 64) (Arg.var ld_7)) fun p_41 =>
            eLit2p1Addr pWvec lit fun q5 =>
            Expr.load i32 (Arg.var q5) fun ld8 =>
            Expr.let_ (wpOp1 (.zext 32 64) (Arg.var ld8)) fun q6 =>
            Expr.jump JsE.fst (Arg.var p_41.fst, Arg.var q6.fst, ()))
           (Expr.jump JsE.fst (Arg.var off, Arg.var sz, ())))
        (Expr.jump Js.fst (Arg.var off, Arg.var sz, Arg.var p_29.fst, ()))) Blocks.nil) fun JsN1 =>
    Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun q1 =>
    Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_28.fst) (Arg.var q1.fst)) fun q2 =>
    Expr.jnz (Arg.var q2.fst)
      (Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun q3 =>
       Expr.jump JsN1.fst (Arg.var q3.fst, ()))
      (Expr.jump JsN1.fst (Arg.var p_28.fst, ()))) Blocks.nil) fun JsN0 =>
  Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var sz) (Arg.imm 0)) fun q1 =>
  Expr.jnz (Arg.var q1.fst) (Expr.jump JsN0.fst (Arg.imm 2, ()))
    (Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun q2 =>
     Expr.let_ (wpOp2 (.shl i64) (Arg.var sz) (Arg.var q2.fst)) fun q3 =>
     Expr.jump JsN0.fst (Arg.var q3.fst, ()))

private theorem wpush_caseD_step8_wp {Γ : Env}
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wstk1 wsort1 : List (BitVec 32)} {wlen1 : Nat} {wus1 : BitVec 64}
    {off32 sz32 lit w0 w1 cnt : Val i32} {m1 : Mem 64}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw1_pos : 1 ≤ wlen1)
    (hlen1 : FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hlay1 : WatchStackLayout
      { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 })
    (hpres1 : WatchPresAll s
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hoff1 : off32.toNat = wOff wvec1 lit.toNat) (hsz1 : sz32.toNat = wSz wvec1 lit.toNat)
    (hm1 : (FullMem c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushCaseDExpr c.hdr c.pWvec c.pWstk (BitVec.ofNat 64 c.wcap)
      (off32.setWidth 64) (sz32.setWidth 64) (cnt.setWidth 64) lit w0 w1 cnt) m1 := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco1 := hlen1.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco1.cur_vars_le
  have hwle1 : wlen1 ≤ c.wcap := hco1.wlen_le
  have hlit2 := bv64_lit2 (lit := lit); have hlit2p1 := bv64_lit2p1 (lit := lit)
  have hoff1_le : wOff wvec1 lit.toNat + wSz wvec1 lit.toNat ≤ wlen1 :=
    hlay1.bounds lit.toNat (hpres1.1 ▸ hlit_lt)
  dsimp only [wpushCaseDExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  refine wp_join_group (fun (ncap0, ()) mN0 => ncap0.toNat < 2 ^ 30 ∧ m1 = mN0) ?_ ?_
  · rintro _ ⟨ncap0, ⟨⟩⟩ mN0 ⟨hnc0_lt, hmN0⟩; rcases hmN0 with rfl; c0_to_group
    refine wp_join_group (fun (ncap1, ()) mN1 =>
      wSz wvec1 lit.toNat + cnt.toNat ≤ ncap1.toNat ∧ ncap1.toNat < 2 ^ 30 ∧ m1 = mN1) ?_ ?_
    · rintro _ ⟨ncap1, ⟨⟩⟩ mN1 ⟨hnc1_ge, hnc1_lt, hmN1⟩; rcases hmN1 with rfl; c0_to_group
      refine wp_join_group (fun (offD, szD, ncapD, ()) mD =>
        ∃ (wvecD wstkD wsortD : List (BitVec 32)) (wlenD : Nat) (wusD : BitVec 64),
          let sD : FullState :=
            { s with
              core := { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD }
              scratch := { s.scratch with wsort := wsortD } }
          1 ≤ wlenD ∧ sD.LengthsOk c ∧ WatchStackLayout sD.core ∧ WatchPresAll s sD ∧
          offD.toNat = wOff wvecD lit.toNat ∧ szD.toNat = wSz wvecD lit.toNat ∧
          szD.toNat + cnt.toNat ≤ ncapD.toNat ∧ ncapD.toNat ≤ c.wcap - wlenD ∧
          (FullMem c sD ⋆ R) mD) ?_ ?_
      · rintro _ ⟨offD, szD, ncapD, ⟨⟩⟩ mD ⟨wvecD, wstkD, wsortD, wlenD, wusD, hwd1, hlenD, hlayD,
          hpresD, hoffD, hszD, hnc_ge, hnc_fit, hmD⟩
        exact wpush_reloc_step8_wp hlit_lt hcnt12 hw0 hw1 hwd1 hlenD hlayD hpresD hoffD hszD
          hnc_ge hnc_fit hmD hQ
      · intro JD hJD; c0_to_group
        · refine wp_join_group (fun (offE, szE, ()) mE =>
            ∃ (wvecE wstkE wsortE : List (BitVec 32)) (wlenE : Nat),
              let sE : FullState :=
                { s with
                  core :=
                    { s.core with wvec := wvecE, wstk := wstkE, wlen := wlenE, wusable := 0#64 }
                  scratch := { s.scratch with wsort := wsortE } }
              1 ≤ wlenE ∧ sE.LengthsOk c ∧ WatchStackLayout sE.core ∧ WatchPresAll s sE ∧
              offE.toNat = wOff wvecE lit.toNat ∧ szE.toNat = wSz wvecE lit.toNat ∧
              (FullMem c sE ⋆ R) mE) ?_ ?_
          · rintro _ ⟨offE, szE, ⟨⟩⟩ mE ⟨wvecE, wstkE, wsortE, wlenE, hwe1, hlenE, hlayE, hpresE,
              hoffE, hszE, hmE⟩
            have hwleE : wlenE ≤ c.wcap := hlenE.core_ok.wlen_le
            have hszE_eq : szE.toNat = wSz wvec1 lit.toNat := by
              have h1 := (hpresE.2 lit.toNat hlit_lt).1
              have h2 := (hpres1.2 lit.toNat hlit_lt).1
              change wSz wvecE lit.toNat = wSz s.core.wvec lit.toNat at h1
              change wSz wvec1 lit.toNat = wSz s.core.wvec lit.toNat at h2; omega
            clear hm1 hlen1 hco1 hlay1 hpres1; c0_to_group
            refine wp_join_group (fun (ncapE, ()) mN =>
              szE.toNat + cnt.toNat ≤ ncapE.toNat ∧ ncapE.toNat < 2 ^ 30 ∧ mE = mN) ?_ ?_
            · rintro _ ⟨ncapE, ⟨⟩⟩ mN ⟨hncE_ge, hncE_lt, hmN⟩; rcases hmN with rfl; c0_usteps
              · exact hQ false wvecE wstkE wlenE 0#64 wsortE mE hlenE hlayE
                  (fun l hl _ => hpresE.2 l hl) (fun h => by cases h)
                  (fun _ => ⟨fun hl => hpresE.2 lit.toNat hl, Or.inr (Or.inr (Or.inr rfl))⟩) hmE
              · exact hJD _ _ ⟨wvecE, wstkE, wsortE, wlenE, 0#64, hwe1, hlenE, hlayE, hpresE,
                  hoffE, hszE, hncE_ge, by omega, hmE⟩
            · intro JN hJN; clear hQ hJD hlenE hlayE hpresE; c0_usteps
              · have hsc : (szE + cnt.setWidth 64).toNat = szE.toNat + cnt.toNat := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide)]; omega
                exact hJN _ _ ⟨by omega, by omega, rfl⟩
              · exact hJN _ _ ⟨by omega, hnc1_lt, rfl⟩
          · intro JE hJE; clear hQ hJD; c0_to_group
            · c0_call hDefrag; refine ⟨c, _, R, rfl, hlen1, hlay1, hm1, ?_⟩
              intro wvecE wstkE wlenE wsortE mE; dsimp only; intro hlenE hlayE h1E hpresE hmE
              have hwvlE : wvecE.length = 4 * c.max_vars := hlenE.core_ok.wvec_len
              have hlit2_ltE : (lit.setWidth 64 <<< (1 : Nat)).toNat < wvecE.length := by omega
              have hlit2p1_ltE : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat < wvecE.length := by
                omega
              c0_usteps
              exact hJE _ _ ⟨wvecE, wstkE, wsortE, wlenE, h1E hw1_pos, hlenE, hlayE,
                watchPresAll_trans hpres1 ⟨rfl, hpresE⟩,
                wpush_getElem_toNat hlit2_ltE hlit2,
                wpush_getElem_toNat hlit2p1_ltE hlit2p1, hmE⟩
            · have hus0 : wus1 = 0#64 := bv64_eq_zero_of_not_pos (by omega)
              have hm1' : (FullMem c { s with
                core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                      wusable := 0#64 }
                scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1 := by
                rw [← hus0]; exact hm1
              exact hJE _ _ ⟨wvec1, wstk1, wsort1, wlen1, hw1_pos,
                { core_ok := { hco1 with wlen_le := hco1.wlen_le }
                  scratch_ok := hlen1.scratch_ok },
                hlay1.with_wstk rfl rfl rfl rfl, hpres1,
                by rw [zext_toNat _ (by decide)]; exact hoff1,
                by rw [zext_toNat _ (by decide)]; exact hsz1, hm1'⟩
        · exact hJD _ _ ⟨wvec1, wstk1, wsort1, wlen1, wus1, hw1_pos,
            hlen1, hlay1, hpres1, by rw [zext_toNat _ (by decide)]; exact hoff1,
            by rw [zext_toNat _ (by decide)]; exact hsz1,
            by rw [zext_toNat _ (by decide), hsz1]; exact hnc1_ge,
            by omega, hm1⟩
    · intro JN1 hJN1; clear hQ; c0_usteps
      · have hsc : (sz32.setWidth 64 + cnt.setWidth 64).toNat =
            wSz wvec1 lit.toNat + cnt.toNat := by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hsz1]; omega
        exact hJN1 _ _ ⟨by omega, by omega, rfl⟩
      · have hsc : (sz32.setWidth 64 + cnt.setWidth 64).toNat =
            wSz wvec1 lit.toNat + cnt.toNat := by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hsz1]; omega
        have : ¬ (ncap0.toNat < (sz32.setWidth 64 + cnt.setWidth 64).toNat) := by c0_bound
        exact hJN1 _ _ ⟨by omega, hnc0_lt, rfl⟩
  · intro JN0 hJN0; clear hQ; c0_usteps
    · exact hJN0 _ _ ⟨by simp, rfl⟩
    · have hsh : (sz32.setWidth 64 <<< (1 : Nat)).toNat = 2 * wSz wvec1 lit.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hsz1]; simp [Nat.shiftLeft_eq]; omega
      exact hJN0 _ _ ⟨by omega, rfl⟩

private abbrev wpushSlowCaseAExpr (h pWvec pWstk wcap cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[]]) (fun _JsA => Blocks.cons (fun (_ : Tup Val []) =>
    eHdrLd h 56 fun ld_5 =>
    Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld_5)) fun p_29 =>
    Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var cVal) (Arg.var p_29.fst)) fun p_30 =>
    Expr.jnz (Arg.var p_30.fst) (Expr.ret (Arg.imm false, ()))
      (eHdrLd h 56 fun ld_6 =>
       eIdx4 pWstk ld_6 fun p_33 =>
       Expr.store (t := i32) (Arg.var w0) (Arg.var p_33)
         (Expr.group (sig := [[]]) (fun _JsW => Blocks.cons (fun (_ : Tup Val []) =>
           eLit2Addr pWvec lit fun p_39 =>
           Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var ld_6)) fun p_40 =>
           Expr.store (t := i32) (Arg.var p_40.fst) (Arg.var p_39)
             (eLit2p1Addr pWvec lit fun p_46 =>
              Expr.store (t := i32) (Arg.var cnt) (Arg.var p_46)
                (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_6) (Arg.var cVal)) fun p_47 =>
                 eHdrSt h 56 (Arg.var p_47.fst) (Expr.ret (Arg.imm true, ()))))) Blocks.nil)
           fun JsW =>
           Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_34 =>
           Expr.jnz (Arg.var p_34.fst)
             (eAddIdx4 pWstk ld_6 (Arg.imm 1) fun p_37 =>
              Expr.store (t := i32) (Arg.var w1) (Arg.var p_37) (Expr.jump JsW.fst ()))
             (Expr.jump JsW.fst ())))) Blocks.nil) fun Js =>
  eHdrLd h 56 fun ld =>
  Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld)) fun p_28 =>
  Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var cVal) (Arg.var p_28.fst)) fun p_29 =>
  Expr.jnz (Arg.var p_29.fst)
    (eHdrLd h 464 fun ld2 =>
     Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var ld2) (Arg.imm 0)) fun p_31 =>
     Expr.jnz (Arg.var p_31.fst)
       (Expr.call (as := [i64]) (bs := []) "full_wstack_defrag_m6" (Arg.var h, ()) fun _ =>
        Expr.jump Js.fst ())
       (Expr.jump Js.fst ()))
    (Expr.jump Js.fst ())

private theorem wpush_slow_caseA_step8_wp {Γ : Env}
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wstk1 wsort1 : List (BitVec 32)} {wlen1 : Nat} {wus1 : BitVec 64}
    {lit w0 w1 cnt : Val i32} {m1 : Mem 64}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw1_pos : 1 ≤ wlen1) (hsz0 : wSz wvec1 lit.toNat = 0)
    (hlen1 : FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hlay1 : WatchStackLayout
      { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 })
    (hpres1 : WatchPresAll s
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hm1 : (FullMem c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushSlowCaseAExpr c.hdr c.pWvec c.pWstk (BitVec.ofNat 64 c.wcap)
      (cnt.setWidth 64) lit w0 w1 cnt) m1 := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco1 := hlen1.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco1.cur_vars_le
  have hwle1 : wlen1 ≤ c.wcap := hco1.wlen_le
  have hlit2 := bv64_lit2 (lit := lit); have hlit2p1 := bv64_lit2p1 (lit := lit)
  dsimp only [wpushSlowCaseAExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  refine wp_join_group (fun _ mA =>
    ∃ (wvecA wstkA wsortA : List (BitVec 32)) (wlenA : Nat) (wusA : BitVec 64),
      let sA : FullState :=
        { s with
          core := { s.core with wvec := wvecA, wstk := wstkA, wlen := wlenA, wusable := wusA }
          scratch := { s.scratch with wsort := wsortA } }
      1 ≤ wlenA ∧ (c.wcap - wlenA < cnt.toNat → wusA = 0#64) ∧
      sA.LengthsOk c ∧ WatchStackLayout sA.core ∧ WatchPresAll s sA ∧ (FullMem c sA ⋆ R) mA) ?_ ?_
  · rintro _ _ mA ⟨wvecA, wstkA, wsortA, wlenA, wusA, hwa1, hwa_oom, hlenA, hlayA, hpresA, hmA⟩
    have hszA0 : wSz wvecA lit.toNat = 0 := by
      have h1 := (hpresA.2 lit.toNat hlit_lt).1
      have h2 := (hpres1.2 lit.toNat hlit_lt).1
      change wSz wvecA lit.toNat = wSz s.core.wvec lit.toNat at h1
      change wSz wvec1 lit.toNat = wSz s.core.wvec lit.toNat at h2; omega
    clear hm1 hlen1 hco1 hlay1 hpres1 hw1_pos hwle1
    have hcoA := hlenA.core_ok
    have hwvlA : wvecA.length = 4 * c.max_vars := hcoA.wvec_len
    have hwslA : wstkA.length = c.wcap := hcoA.wstk_len_arr
    have hwleA : wlenA ≤ c.wcap := hcoA.wlen_le
    c0_to_group
    · have hlt_oom : c.wcap - wlenA < cnt.toNat := by omega
      have husA0 : wusA = 0#64 := hwa_oom hlt_oom
      subst husA0
      exact hQ false wvecA wstkA wlenA 0#64 wsortA mA hlenA hlayA
        (fun l hl _ => hpresA.2 l hl) (fun h => by cases h)
        (fun _ => ⟨fun hl => hpresA.2 lit.toNat hl, Or.inr (Or.inr (Or.inr rfl))⟩) hmA
    · have hwa_fit : cnt.toNat ≤ c.wcap - wlenA := by omega
      clear hc hwa_oom
      have hpos_eq : (BitVec.ofNat 64 wlenA).toNat = wlenA := bv64_ofNat_toNat (by omega)
      have hpos_p1 : (BitVec.ofNat 64 wlenA + 1).toNat = wlenA + 1 := by
        rw [BitVec.toNat_add, hpos_eq]; simp; omega
      c0_to_group
      refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
        (∀ idx < wlenA, wstkW[idx]? = wstkA[idx]?) ∧ wstkW[wlenA]? = some w0 ∧
        (cnt.toNat = 2 → wstkW[wlenA + 1]? = some w1) ∧
        (FullMem c { s with
          core := { s.core with wvec := wvecA, wstk := wstkW, wlen := wlenA, wusable := wusA }
          scratch := { s.scratch with wsort := wsortA } } ⋆ R) mW) ?_ ?_
      · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; c0_usteps
        have hpos32 := bv32_trunc_ofNat (n := wlenA) (by omega)
        have hnew_wlen : (BitVec.ofNat 64 wlenA + cnt.setWidth 64).toNat = wlenA + cnt.toNat := by
          rw [BitVec.toNat_add, hpos_eq, zext_toNat _ (by decide)]; omega
        have hev := wvec_set_even_u (wvec := wvecA) (l := lit.toNat)
          (v := (BitVec.ofNat 64 wlenA).setWidth 32) (by omega)
        have hod := wvec_set_odd_u (wvec := wvecA.set (2 * lit.toNat)
          ((BitVec.ofNat 64 wlenA).setWidth 32)) (l := lit.toNat) (v := cnt)
          (by rw [List.length_set]; omega)
        have hfin := wpush_finalize (s := s)
          (s2 := { s with
            core := { s.core with wvec := wvecA, wstk := wstkA, wlen := wlenA, wusable := wusA }
            scratch := { s.scratch with wsort := wsortA } })
          (lit := lit.toNat) (cnt := cnt.toNat) (dst := wlenA)
          (wlen' := (BitVec.ofNat 64 wlenA + cnt.setWidth 64).toNat)
          (wvec' := (wvecA.set (lit.setWidth 64 <<< (1 : Nat)).toNat
              ((BitVec.ofNat 64 wlenA).setWidth 32)).set
              ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat) cnt)
          (wstk' := wstkW) (wsort' := wsortA) hlayA hpresA hlit_lt hcnt12 hw0 hw1
          (by dsimp only; omega) hwa1 (by dsimp only; omega)
          (fun j hj hne => by
            rw [wOff, wSz, hlit2, hlit2p1, (hod j).1, (hev j).2.1 hne, (hod j).2.1 hne,
              (hev j).1]
            exact ⟨rfl, rfl⟩)
          (by rw [wOff, hlit2, hlit2p1, (hod lit.toNat).1, (hev lit.toNat).2.2,
            Option.getD_some, hpos32])
          (by rw [wSz, hlit2, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hszA0, Nat.zero_add])
          (fun j hj _ _ => Or.inl (hlayA.bounds j (hpresA.1 ▸ hj)))
          (fun j hj _ k hk => by
            have hbj := hlayA.bounds j (hpresA.1 ▸ hj)
            change wOff wvecA j + wSz wvecA j ≤ wlenA at hbj
            dsimp only at hk ⊢; exact hpreW _ (by omega))
          (fun k hk => by dsimp only at hk ⊢; omega)
          (by dsimp only; rw [hszA0, Nat.add_zero]; exact hat0W)
          (fun hc2 => by dsimp only; rw [hszA0, Nat.add_zero]; exact hat1W hc2) wusA
        exact hQ true _ wstkW _ wusA wsortA _
          { core_ok := { hcoA with wvec_len := by rw [List.length_set, List.length_set, hwvlA],
                                   wstk_len_arr := hwsW, wlen_le := by dsimp only; omega }
            scratch_ok := hlenA.scratch_ok }
          hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
      · intro JW hJW; clear hQ hlenA hcoA hlayA hpresA; c0_split
        · have hc2 := bv32_eq_nat 2 (by decide) hc; c0_usteps
          refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwslA],
            fun idx hidx => by
              rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)],
            by rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by omega)],
            fun _ => by rw [hpos_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
        · c0_usteps; have hne2 := bv32_ne_nat 2 (by decide) hc
          refine hJW _ _ ⟨_, by rw [List.length_set, hwslA],
            fun idx hidx => by rw [hpos_eq, List.getElem?_set_ne (by omega)],
            by rw [hpos_eq, List.getElem?_set_self (by omega)], fun hc2 => absurd hc2 hne2, hm⟩
  · intro JA hJA; clear hQ; c0_to_group
    · c0_call hDefrag; refine ⟨c, _, R, rfl, hlen1, hlay1, hm1, ?_⟩
      intro wvecA wstkA wlenA wsortA mA; dsimp only; intro hlenA hlayA h1A hpresA hmA; c0_usteps
      exact hJA _ _ ⟨wvecA, wstkA, wsortA, wlenA, 0#64, h1A hw1_pos, fun _ => rfl, hlenA, hlayA,
        watchPresAll_trans hpres1 ⟨rfl, hpresA⟩, hmA⟩
    · have hus0 : wus1 = 0#64 := bv64_eq_zero_of_not_pos (by omega)
      have hm1' : (FullMem c { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1 := by
        rw [← hus0]; exact hm1
      exact hJA _ _ ⟨wvec1, wstk1, wsort1, wlen1, 0#64, hw1_pos, fun _ => rfl,
        { core_ok := { hco1 with wlen_le := hco1.wlen_le }, scratch_ok := hlen1.scratch_ok },
        hlay1.with_wstk rfl rfl rfl rfl, hpres1, hm1'⟩
    · exact hJA _ _ ⟨wvec1, wstk1, wsort1, wlen1, wus1, hw1_pos,
        fun _ => by omega, hlen1, hlay1, hpres1, hm1⟩

/-- Step-8 cold fallback `full_watch_push_slow_m6` (`75%` proactive defrag guard) satisfies
canonical `Full.fullWatchPushSpec` parametrically in `Γ`. -/
theorem full_watch_push_slow_m6_step8_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Func.wp Γ full_watch_push_slow_m6_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco.cur_vars_le
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]; simp [Nat.shiftLeft_eq]; omega
  have hwvl := hco.wvec_len; have hwsl := hco.wstk_len_arr; have hwle := hco.wlen_le
  c0_to_group
  · have hge : 2 * s.core.cur_vars ≤ lit.toNat := by omega
    exact hQ false s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.scratch.wsort m hlen hlay
      (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
      (fun _ => ⟨fun h => by omega, Or.inl (by omega)⟩) hm
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
    clear hc
    refine wp_join_group (fun _ m0 => (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧ m = m0) ?_ ?_
    rotate_left
    · intro J0 hJ0; c0_usteps
      · rename_i hc1
        exact hQ false s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.scratch.wsort m hlen
          hlay (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
          (fun _ => ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩,
            Or.inr (Or.inl ⟨bv32_ne_nat 1 (by decide) hc1, bv32_ne_nat 2 (by decide) hc⟩)⟩) hm
      · exact hJ0 _ _ ⟨Or.inr (bv32_eq_nat 2 (by decide) hc), rfl⟩
      · exact hJ0 _ _ ⟨Or.inl (bv32_eq_nat 1 (by decide) hc), rfl⟩
    rintro _ _ m0 ⟨hcnt12, hm0⟩; rcases hm0 with rfl
    have hlit2 := bv64_lit2 (lit := lit); have hlit2p1 := bv64_lit2p1 (lit := lit)
    c0_to_group
    refine wp_join_group (fun _ m1 => ∃ (wstk1 : List (BitVec 32)) (wlen1 : Nat),
      let s1 : FullState := { s with core := { s.core with wstk := wstk1, wlen := wlen1 } }
      1 ≤ wlen1 ∧ s1.LengthsOk c ∧ WatchStackLayout s1.core ∧ WatchPresAll s s1 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨wstk1, wlen1, hw1_pos, hlen1, hlay1, hpres1, hm1⟩; clear hm
      c0_to_group
      refine wp_join_group (fun _ m2 =>
        ∃ (wvec2 wstk2 wsort2 : List (BitVec 32)) (wlen2 : Nat) (wus2 : BitVec 64),
          let s2 : FullState :=
            { s with
              core := { s.core with wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wus2 }
              scratch := { s.scratch with wsort := wsort2 } }
          1 ≤ wlen2 ∧ s2.LengthsOk c ∧ WatchStackLayout s2.core ∧ WatchPresAll s s2 ∧
          (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro _ ⟨retry2, ⟨⟩⟩ m2 ⟨wvec2, wstk2, wsort2, wlen2, wus2, hw2_pos, hlen2, hlay2, hpres2,
          hm2⟩
        have hco2 := hlen2.core_ok
        have hcv2 := hco2.cur_vars_le; have hwv2 := hco2.wvec_len
        dsimp only at hcv2 hwv2
        have hlit2_lt : (lit.setWidth 64 <<< (1 : Nat)).toNat < wvec2.length := by
          rw [hlit2]; omega
        have hlit2p1_lt : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat < wvec2.length := by
          rw [hlit2p1]; omega
        have hoff2 : (wvec2[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).toNat =
            wOff wvec2 lit.toNat := wpush_getElem_toNat hlit2_lt hlit2
        have hsz2 : (wvec2[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt).toNat =
            wSz wvec2 lit.toNat := wpush_getElem_toNat hlit2p1_lt hlit2p1
        have hoff2_le : wOff wvec2 lit.toNat + wSz wvec2 lit.toNat ≤ wlen2 :=
          hlay2.bounds lit.toNat (hpres2.1 ▸ hlit_lt)
        c0_to_group
        generalize hoffV :
          wvec2[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt = off32 at hoff2 ⊢
        generalize hszV :
          wvec2[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt = sz32 at hsz2 ⊢
        clear hoffV hszV
        refine wp_join_group
          (fun _ mA0 => ¬ (wSz wvec2 lit.toNat = 0 ∧ wOff wvec2 lit.toNat = 0) ∧
            m2 = mA0) ?_ ?_
        · rintro _ _ mA0 ⟨hnot00, hmA0⟩; rcases hmA0 with rfl
          have hoff2_pos : 1 ≤ wOff wvec2 lit.toNat := by
            by_cases hszp : 0 < wSz wvec2 lit.toNat
            · exact hlay2.pos_off lit.toNat (hpres2.1 ▸ hlit_lt) hszp
            · omega
          have hend_eq : (off32.setWidth 64 + sz32.setWidth 64).toNat =
              wOff wvec2 lit.toNat + wSz wvec2 lit.toNat := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hoff2, hsz2]
            omega
          c0_to_group
          refine wp_join_group (fun _ mD0 => m2 = mD0) ?_ ?_
          · rintro _ _ mD0 hmD0; rcases hmD0 with rfl
            exact wpush_caseD_step8_wp hDefrag hlit_lt hcnt12 hw0 hw1 hw2_pos hlen2 hlay2 hpres2
              hoff2 hsz2 hm2 hQ
          · intro JD hJD
            c0_split
            · c0_to_group
              refine wp_join_group (fun _ mC0 => m2 = mC0) ?_ ?_
              · rintro _ _ mC0 hmC0; rcases hmC0 with rfl
                exact wpush_caseC_step8_wp hlit_lt hcnt12 hw0 hw1 hoff2_pos hlen2 hlay2 hpres2
                  hend_eq hsz2 hm2 (hJD () m2 rfl) hQ
              · intro JC hJC
                exact wpush_caseB_step8_wp hlit_lt hcnt12 hw0 hw1 hoff2_pos hlen2 hlay2 hpres2
                  hend_eq hsz2 hm2 (hJC () m2 rfl) hQ
            · exact hJD () m2 rfl
        · intro JnotA hJnotA; clear hnlits hwsl hwle; c0_to_group
          · rename_i hsz_c
            have hsz0 : wSz wvec2 lit.toNat = 0 := by
              have := congrArg BitVec.toNat hsz_c
              rw [zext_toNat _ (by decide), hsz2] at this; exact this
            clear hJnotA hsz_c hc
            exact wpush_slow_caseA_step8_wp hDefrag hlit_lt hcnt12 hw0 hw1 hw2_pos hsz0 hlen2
              hlay2 hpres2 hm2 hQ
          · exact hJnotA _ _ ⟨fun ⟨_, hoff0⟩ => hc (BitVec.eq_of_toNat_eq
              (by rw [zext_toNat _ (by decide), hoff2]; exact hoff0)), rfl⟩
          · exact hJnotA _ _ ⟨fun ⟨hsz0, _⟩ =>
              hc (BitVec.eq_of_toNat_eq (by rw [zext_toNat _ (by decide), hsz2]; exact hsz0)), rfl⟩
      · intro Jpro hJpro; clear hQ
        c0_split
        · c0_split
          · c0_usteps; c0_call hDefrag
            refine ⟨c, _, R, rfl, hlen1, hlay1, hm1, ?_⟩
            intro wvecD wstkD wlenD wsortD mD; dsimp only; intro hlenD hlayD h1D hpresD hmD
            exact hJpro _ _ ⟨wvecD, wstkD, wsortD, wlenD, 0#64, h1D hw1_pos, hlenD, hlayD,
              watchPresAll_trans hpres1 ⟨rfl, hpresD⟩, hmD⟩
          · c0_usteps
            exact hJpro _ _ ⟨s.core.wvec, wstk1, s.scratch.wsort, wlen1, s.core.wusable, hw1_pos,
              hlen1, hlay1, hpres1, hm1⟩
        · c0_usteps
          exact hJpro _ _ ⟨s.core.wvec, wstk1, s.scratch.wsort, wlen1, s.core.wusable, hw1_pos,
            hlen1, hlay1, hpres1, hm1⟩
    · intro J1 hJ1; faa_head_steps
      refine wp_jnz_of (fun hc_w0 => ?_) (fun hc_ne0 => ?_)
      · simp only [Arg.val_var] at hc_w0; c0_cond hc_w0
        have hw0_eq : s.core.wlen = 0 := by
          have := bv64_ofNat_toNat (n := s.core.wlen) (by omega)
          rw [hc_w0] at this; simpa using this.symm
        clear hc_w0; faa_head_steps
        refine wp_jnz_of (fun hc_lt => ?_) (fun hc_ge => ?_)
        · clear hJ1 hc_lt; c0_usteps
          exact hQ false s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.scratch.wsort m hlen
            hlay (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
            (fun _ => ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩, Or.inr (Or.inr (Or.inl rfl))⟩) hm
        · simp only [Arg.val_var] at hc_ge; c0_cond hc_ge
          have hcap1 : 1 ≤ c.wcap := by omega
          have hwstk_pos : 0 < s.core.wstk.length := by omega
          clear hQ hc_ge; c0_usteps
          have hsz_all0 : ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore s.core l = 0 :=
            fun l hl => by have := hlay.bounds l hl; omega
          refine hJ1 (true, ()) _ ⟨s.core.wstk.set 0 0#32, 1, by omega,
            { core_ok := { hco with wstk_len_arr := by rw [List.length_set, hwsl],
                                    wlen_le := by dsimp only; omega }
              scratch_ok := hlen.scratch_ok },
            ⟨fun l hl => by
                change fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ 1
                have := hlay.bounds l hl; omega,
             fun l hl hpos => by
                change 0 < fullWatchSizeCore s.core l at hpos
                have := hsz_all0 l hl; omega,
             fun l1 _ h1 _ _ hp1 _ => by
                change 0 < fullWatchSizeCore s.core l1 at hp1
                have := hsz_all0 l1 h1; omega,
             fun l hl k hk => by
                change k < fullWatchSizeCore s.core l at hk
                have := hsz_all0 l hl; omega⟩,
            ⟨rfl, fun l hl => ⟨rfl, fun k hk => by
                change k < fullWatchSizeCore s.core l at hk
                have := hsz_all0 l hl; omega⟩⟩, hm⟩
      · simp only [Arg.val_var] at hc_ne0; c0_cond hc_ne0
        have hw1_pos : 1 ≤ s.core.wlen := by
          have : s.core.wlen ≠ 0 := fun h0 => hc_ne0 (by simp [h0])
          omega
        clear hQ hc_ne0; c0_usteps
        exact hJ1 (false, ()) _ ⟨s.core.wstk, s.core.wlen, hw1_pos, hlen, hlay,
          watchPresAll_refl s, hm⟩

/-! ## 2. Hot Fast Path `full_watch_push_m6_step8_wp` -/

private abbrev s8FastCaseBExpr (h pWstk endVal wlen l2 cVal : Val i64)
    (w0 w1 : Val i32) (JB : Cont []) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var endVal) (Arg.var wlen)) fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
    (eHdrLd h 40 fun wcapV =>
     Expr.let_ (wpOp2 (.sub i64) (Arg.var wcapV) (Arg.var wlen)) fun p_28 =>
     Expr.let_ (wpOp2 (.cmp .ule i64 .bool rfl) (Arg.var cVal) (Arg.var p_28.fst)) fun p_29 =>
     Expr.jnz (Arg.var p_29.fst)
       (eIdx4 pWstk endVal fun p_31 =>
        Expr.store (t := i32) (Arg.var w0) (Arg.var p_31)
          (Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun (_ : Tup Val []) =>
            eHdrLd h 104 fun wvecV =>
            eAddIdx4 wvecV l2 (Arg.imm 1) fun p_36 =>
            eAddIdx4 wvecV l2 (Arg.imm 1) fun p_39 =>
            Expr.load i32 (Arg.var p_39) fun ld_s =>
            Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var cVal)) fun p_40 =>
            Expr.let_ (wpOp2 (.add i32) (Arg.var ld_s) (Arg.var p_40.fst)) fun p_41 =>
            Expr.store (t := i32) (Arg.var p_41.fst) (Arg.var p_36)
              (Expr.let_ (wpOp2 (.add i64) (Arg.var endVal) (Arg.var cVal)) fun p_42 =>
               eHdrSt h 56 (Arg.var p_42.fst) (Expr.ret (Arg.imm true, ())))) Blocks.nil)
            fun Js =>
            Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var cVal) (Arg.imm 2)) fun p_32 =>
            Expr.jnz (Arg.var p_32.fst)
              (eAddIdx4 pWstk endVal (Arg.imm 1) fun p_35 =>
               Expr.store (t := i32) (Arg.var w1) (Arg.var p_35) (Expr.jump Js.fst ()))
              (Expr.jump Js.fst ())))
       (Expr.jump JB ()))
    (Expr.jump JB ())

private theorem s8FastCaseB_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {endVal : Val i64} {sz32 lit w0 w1 cnt : Val i32}
    {m : Mem 64} {JB : Cont []}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hlen : FullState.LengthsOk c s) (hlay : WatchStackLayout s.core)
    (hlit2p1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * lit.toNat + 1)
    (hcnt_tr : (cnt.setWidth 64).setWidth 32 = cnt)
    (hoff_pos : 1 ≤ wOff s.core.wvec lit.toNat) (hsz : sz32.toNat = wSz s.core.wvec lit.toNat)
    (hget_sz : ∀ pf, s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'pf = sz32)
    (hend_eq : endVal.toNat = wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat)
    (hm : (FullMem c s ⋆ R) m) (hJB : JB () m) (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (s8FastCaseBExpr c.hdr c.pWstk endVal (BitVec.ofNat 64 s.core.wlen)
      (lit.setWidth 64 <<< (1 : Nat)) (cnt.setWidth 64) w0 w1 JB) m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco.cur_vars_le
  have hwvl := hco.wvec_len; have hwsl := hco.wstk_len_arr; have hwle := hco.wlen_le
  have hoff_le := hlay.bounds lit.toNat hlit_lt
  dsimp only [s8FastCaseBExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4]
  c0_split
  · have hend_wlen : wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat = s.core.wlen := by
      have := congrArg BitVec.toNat hc
      rw [hend_eq, bv64_ofNat_toNat (by omega)] at this; exact this
    clear hc
    c0_split
    · have hfitB : cnt.toNat ≤ c.wcap - s.core.wlen := by omega
      clear hc; c0_to_group
      refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
        (∀ idx < s.core.wlen, wstkW[idx]? = s.core.wstk[idx]?) ∧
        wstkW[s.core.wlen]? = some w0 ∧
        (cnt.toNat = 2 → wstkW[s.core.wlen + 1]? = some w1) ∧
        (FullMem c { s with core := { s.core with wstk := wstkW } } ⋆ R) mW) ?_ ?_
      · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; c0_usteps
        rw [hget_sz] at hm
        have hsz_new : (sz32 + cnt).toNat = wSz s.core.wvec lit.toNat + cnt.toNat := by
          rw [BitVec.toNat_add, hsz]; omega
        have hwlen_new : (endVal + cnt.setWidth 64).toNat = s.core.wlen + cnt.toNat := by
          rw [BitVec.toNat_add, hend_eq, hend_wlen, zext_toNat _ (by decide)]; omega
        have hod := wvec_set_odd_u (wvec := s.core.wvec) (l := lit.toNat)
          (v := sz32 + (cnt.setWidth 64).setWidth 32) (by omega)
        have hsz_tr : (sz32 + (cnt.setWidth 64).setWidth 32).toNat =
            wSz s.core.wvec lit.toNat + cnt.toNat := by
          rw [hcnt_tr]; exact hsz_new
        have hfin := wpush_finalize (s := s) (s2 := s)
          (lit := lit.toNat) (cnt := cnt.toNat) (dst := wOff s.core.wvec lit.toNat)
          (wlen' := (endVal + cnt.setWidth 64).toNat)
          (wvec' := s.core.wvec.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
            (sz32 + (cnt.setWidth 64).setWidth 32))
          (wstk' := wstkW) (wsort' := s.scratch.wsort) hlay (watchPresAll_refl s)
          hlit_lt hcnt12 hw0 hw1 (by omega) hoff_pos (by omega)
          (fun j hj hne => by
            rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
          (by rw [wOff, hlit2p1, (hod lit.toNat).1])
          (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_tr])
          (fun j hj hne hszj => by
            have hbj := hlay.bounds j hj
            change wOff s.core.wvec j + wSz s.core.wvec j ≤ s.core.wlen at hbj
            by_cases hszl : 0 < wSz s.core.wvec lit.toNat
            · rcases hlay.disjoint j lit.toNat hj hlit_lt hne hszj hszl with hd | hd
              · exact Or.inl hd
              · change wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat ≤
                  wOff s.core.wvec j at hd; omega
            · exact Or.inl (by omega))
          (fun j hj _ k hk => by
            have hbj := hlay.bounds j hj
            change wOff s.core.wvec j + wSz s.core.wvec j ≤ s.core.wlen at hbj
            exact hpreW _ (by omega))
          (fun k hk => hpreW _ (by omega))
          (by rw [hend_wlen]; exact hat0W)
          (fun hc2 => by rw [hend_wlen]; exact hat1W hc2) s.core.wusable
        exact hQ true _ wstkW _ s.core.wusable s.scratch.wsort _
          { core_ok := { hco with wvec_len := by rw [List.length_set, hwvl],
                                  wstk_len_arr := hwsW,
                                  wlen_le := by
                                    change (endVal + cnt.setWidth 64).toNat ≤ c.wcap; omega }
            scratch_ok := hlen.scratch_ok }
          hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
      · intro JW hJW; clear hQ
        have hend_p1 : (endVal + 1).toNat = s.core.wlen + 1 := by
          rw [BitVec.toNat_add, hend_eq, hend_wlen]; simp; omega
        c0_split
        · have hc2 : cnt.toNat = 2 := by
            have := bv64_eq_nat 2 (by decide) hc
            rw [zext_toNat _ (by decide)] at this; exact this
          c0_usteps
          refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl],
            fun idx hidx => by
              rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)],
            by rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by omega)],
            fun _ => by rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)],
            hm⟩
        · c0_usteps
          have hne2 : cnt.toNat ≠ 2 := by
            have := bv64_ne_nat 2 (by decide) hc
            rw [zext_toNat _ (by decide)] at this; exact this
          refine hJW _ _ ⟨_, by rw [List.length_set, hwsl],
            fun idx hidx => by rw [hend_eq, hend_wlen, List.getElem?_set_ne (by omega)],
            by rw [hend_eq, hend_wlen, List.getElem?_set_self (by omega)],
            fun hc2 => absurd hc2 hne2, hm⟩
    · c0_usteps; exact hJB
  · c0_usteps; exact hJB

private abbrev s8FastCaseAExpr (h wlen l2 cVal : Val i64)
    (w0 w1 : Val i32) (JS : Cont []) : Expr Val Cont [Ty.bool] :=
  eHdrLd h 40 fun wcapV =>
  Expr.let_ (wpOp2 (.sub i64) (Arg.var wcapV) (Arg.var wlen)) fun p_25 =>
  Expr.let_ (wpOp2 (.cmp .ule i64 .bool rfl) (Arg.var cVal) (Arg.var p_25.fst)) fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
    (eHdrLd h 120 fun wstkV =>
     eIdx4 wstkV wlen fun p_29 =>
     Expr.store (t := i32) (Arg.var w0) (Arg.var p_29)
       (Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun (_ : Tup Val []) =>
         eHdrLd h 104 fun wvecV =>
         eIdx4 wvecV l2 fun p_33 =>
         Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var wlen)) fun p_34 =>
         Expr.store (t := i32) (Arg.var p_34.fst) (Arg.var p_33)
           (eAddIdx4 wvecV l2 (Arg.imm 1) fun p_37 =>
            Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var cVal)) fun p_38 =>
            Expr.store (t := i32) (Arg.var p_38.fst) (Arg.var p_37)
              (Expr.let_ (wpOp2 (.add i64) (Arg.var wlen) (Arg.var cVal)) fun p_39 =>
               eHdrSt h 56 (Arg.var p_39.fst) (Expr.ret (Arg.imm true, ()))))) Blocks.nil)
         fun Js =>
         Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var cVal) (Arg.imm 2)) fun p_30 =>
         Expr.jnz (Arg.var p_30.fst)
           (eAddIdx4 wstkV wlen (Arg.imm 1) fun p_33 =>
            Expr.store (t := i32) (Arg.var w1) (Arg.var p_33) (Expr.jump Js.fst ()))
           (Expr.jump Js.fst ())))
    (Expr.jump JS ())

private theorem s8FastCaseA_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {lit w0 w1 cnt : Val i32} {m : Mem 64} {JS : Cont []}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw_pos : 1 ≤ s.core.wlen) (hsz0 : wSz s.core.wvec lit.toNat = 0)
    (hlen : FullState.LengthsOk c s) (hlay : WatchStackLayout s.core)
    (hlit2 : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat)
    (hlit2p1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * lit.toNat + 1)
    (hcnt_tr : (cnt.setWidth 64).setWidth 32 = cnt)
    (hm : (FullMem c s ⋆ R) m) (hJS : JS () m) (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (s8FastCaseAExpr c.hdr (BitVec.ofNat 64 s.core.wlen)
      (lit.setWidth 64 <<< (1 : Nat)) (cnt.setWidth 64) w0 w1 JS) m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco.cur_vars_le
  have hwvl := hco.wvec_len; have hwsl := hco.wstk_len_arr; have hwle := hco.wlen_le
  dsimp only [s8FastCaseAExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4]
  c0_split
  · have hfitA : cnt.toNat ≤ c.wcap - s.core.wlen := by omega
    clear hc
    have hpos_eq : (BitVec.ofNat 64 s.core.wlen).toNat = s.core.wlen :=
      bv64_ofNat_toNat (by omega)
    have hpos_p1 : (BitVec.ofNat 64 s.core.wlen + 1).toNat = s.core.wlen + 1 := by
      rw [BitVec.toNat_add, hpos_eq]; simp; omega
    c0_to_group
    refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
      (∀ idx < s.core.wlen, wstkW[idx]? = s.core.wstk[idx]?) ∧
      wstkW[s.core.wlen]? = some w0 ∧
      (cnt.toNat = 2 → wstkW[s.core.wlen + 1]? = some w1) ∧
      (FullMem c { s with core := { s.core with wstk := wstkW } } ⋆ R) mW) ?_ ?_
    · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; c0_usteps
      have hpos32 := bv32_trunc_ofNat (n := s.core.wlen) (by omega)
      have hc32 : ((cnt.setWidth 64).setWidth 32).toNat = cnt.toNat := by rw [hcnt_tr]
      have hnew_wlen : (BitVec.ofNat 64 s.core.wlen + cnt.setWidth 64).toNat =
          s.core.wlen + cnt.toNat := by
        rw [BitVec.toNat_add, hpos_eq, zext_toNat _ (by decide)]; omega
      have hev := wvec_set_even_u (wvec := s.core.wvec) (l := lit.toNat)
        (v := (BitVec.ofNat 64 s.core.wlen).setWidth 32) (by omega)
      have hod := wvec_set_odd_u (wvec := s.core.wvec.set (2 * lit.toNat)
        ((BitVec.ofNat 64 s.core.wlen).setWidth 32)) (l := lit.toNat)
        (v := (cnt.setWidth 64).setWidth 32) (by rw [List.length_set]; omega)
      have hfin := wpush_finalize (s := s) (s2 := s)
        (lit := lit.toNat) (cnt := cnt.toNat) (dst := s.core.wlen)
        (wlen' := (BitVec.ofNat 64 s.core.wlen + cnt.setWidth 64).toNat)
        (wvec' := (s.core.wvec.set (lit.setWidth 64 <<< (1 : Nat)).toNat
            ((BitVec.ofNat 64 s.core.wlen).setWidth 32)).set
            ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat) ((cnt.setWidth 64).setWidth 32))
        (wstk' := wstkW) (wsort' := s.scratch.wsort) hlay (watchPresAll_refl s)
        hlit_lt hcnt12 hw0 hw1 (by omega) hw_pos (by rw [hsz0]; omega)
        (fun j hj hne => by
          rw [wOff, wSz, hlit2, hlit2p1, (hod j).1, (hev j).2.1 hne, (hod j).2.1 hne,
            (hev j).1]; exact ⟨rfl, rfl⟩)
        (by rw [wOff, hlit2, hlit2p1, (hod lit.toNat).1, (hev lit.toNat).2.2,
          Option.getD_some, hpos32])
        (by rw [wSz, hlit2, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz0,
          hc32, Nat.zero_add])
        (fun j hj _ _ => Or.inl (hlay.bounds j hj))
        (fun j hj _ k hk => by
          have hbj := hlay.bounds j hj
          change wOff s.core.wvec j + wSz s.core.wvec j ≤ s.core.wlen at hbj
          exact hpreW _ (by omega))
        (fun k hk => by omega)
        (by rw [hsz0, Nat.add_zero]; exact hat0W)
        (fun hc2 => by rw [hsz0, Nat.add_zero]; exact hat1W hc2) s.core.wusable
      exact hQ true _ wstkW _ s.core.wusable s.scratch.wsort _
        { core_ok := { hco with wvec_len := by rw [List.length_set, List.length_set, hwvl],
                                wstk_len_arr := hwsW,
                                wlen_le := by
                                  change (BitVec.ofNat 64 s.core.wlen + cnt.setWidth 64).toNat ≤
                                    c.wcap
                                  omega }
          scratch_ok := hlen.scratch_ok }
        hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
          hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
    · intro JW hJW; clear hQ
      c0_split
      · have hc2 : cnt.toNat = 2 := by
          have := bv64_eq_nat 2 (by decide) hc
          rw [zext_toNat _ (by decide)] at this; exact this
        c0_usteps
        refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl],
          fun idx hidx => by
            rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)],
          by rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by omega)],
          fun _ => by rw [hpos_p1, List.getElem?_set_self (by rw [List.length_set]; omega)],
          hm⟩
      · c0_usteps
        have hne2 : cnt.toNat ≠ 2 := by
          have := bv64_ne_nat 2 (by decide) hc
          rw [zext_toNat _ (by decide)] at this; exact this
        refine hJW _ _ ⟨_, by rw [List.length_set, hwsl],
          fun idx hidx => by rw [hpos_eq, List.getElem?_set_ne (by omega)],
          by rw [hpos_eq, List.getElem?_set_self (by omega)],
          fun hc2 => absurd hc2 hne2, hm⟩
  · c0_usteps; exact hJS

/-- Step-8 hot fast path `full_watch_push_m6` (`75%` proactive defrag skip guard) satisfies
canonical `Full.fullWatchPushSpec` parametrically in `Γ`. -/
theorem full_watch_push_m6_step8_wp (Γ : Env)
    (hSlow : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Func.wp Γ full_watch_push_m6_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco.cur_vars_le
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]; simp [Nat.shiftLeft_eq]; omega
  have hwvl := hco.wvec_len; have hwsl := hco.wstk_len_arr; have hwle := hco.wlen_le
  c0_to_group
  · have hge : 2 * s.core.cur_vars ≤ lit.toNat := by omega
    exact hQ false s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.scratch.wsort m hlen hlay
      (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
      (fun _ => ⟨fun h => by omega, Or.inl (by omega)⟩) hm
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
    clear hc
    refine wp_join_group (fun _ m0 => (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧ m = m0) ?_ ?_
    rotate_left
    · intro J0 hJ0; c0_usteps
      · rename_i hc1
        exact hQ false s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.scratch.wsort m hlen
          hlay (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
          (fun _ => ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩,
            Or.inr (Or.inl ⟨bv32_ne_nat 1 (by decide) hc1, bv32_ne_nat 2 (by decide) hc⟩)⟩) hm
      · exact hJ0 _ _ ⟨Or.inr (bv32_eq_nat 2 (by decide) hc), rfl⟩
      · exact hJ0 _ _ ⟨Or.inl (bv32_eq_nat 1 (by decide) hc), rfl⟩
    rintro _ _ m0 ⟨hcnt12, hm0⟩; subst m0
    have hlit2 := bv64_lit2 (lit := lit); have hlit2p1 := bv64_lit2p1 (lit := lit)
    have hcnt_tr : (cnt.setWidth 64).setWidth 32 = cnt := by
      rcases hcnt12 with hc1 | hc2
      · have : cnt = 1#32 := BitVec.eq_of_toNat_eq (by simpa using hc1)
        subst this; decide
      · have : cnt = 2#32 := BitVec.eq_of_toNat_eq (by simpa using hc2)
        subst this; decide
    c0_to_group
    refine wp_join_group (fun _ mS => m = mS) ?_ ?_
    · rintro _ _ mS hmS; subst mS; c0_usteps
      c0_call hSlow
      rw [hcnt_tr]
      exact ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
    · intro JS hJS
      c0_split
      · have hw1_pos : 1 ≤ s.core.wlen := by
          have : s.core.wlen ≠ 0 := fun h0 => hc (by simp [h0])
          omega
        clear hc
        refine wp_join_group (fun _ mF => 1 ≤ s.core.wlen ∧ m = mF) ?_ ?_
        · rintro _ _ mF ⟨hw_pos, hmF⟩; subst mF
          have hlit2_lt : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
            rw [hlit2]; omega
          have hlit2p1_lt : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            rw [hlit2p1]; omega
          have hoff : (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).toNat =
              wOff s.core.wvec lit.toNat := wpush_getElem_toNat hlit2_lt hlit2
          have hsz : (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt).toNat =
              wSz s.core.wvec lit.toNat := wpush_getElem_toNat hlit2p1_lt hlit2p1
          have hoff_le : wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat ≤ s.core.wlen :=
            hlay.bounds lit.toNat hlit_lt
          c0_to_group
          generalize hoffV :
            s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt = off32 at hoff ⊢
          generalize hszV :
            s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt = sz32 at hsz ⊢
          clear hoffV
          have hget_sz : ∀ pf,
              s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'pf = sz32 := fun _ => hszV
          have hend_eq : (off32.setWidth 64 + sz32.setWidth 64).toNat =
              wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hoff, hsz]
            omega
          refine wp_join_group (fun _ m3 => m = m3)
            (fun _ _ m3 hm3 => by subst m3; exact hJS () m rfl) fun J3 hJ3 => ?_
          c0_split
          · have hend_pos : 0 < wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat := by
              have hpos64 : 0 < (off32.toNat + sz32.toNat) % 2 ^ 64 := hc
              omega
            have hoff_pos : 1 ≤ wOff s.core.wvec lit.toNat := by
              by_cases hszp : 0 < wSz s.core.wvec lit.toNat
              · exact hlay.pos_off lit.toNat hlit_lt hszp
              · omega
            clear hc
            c0_to_group
            refine wp_join_group (fun _ mB => m = mB) ?_ ?_
            · rintro _ _ mB hmB; subst mB
              exact s8FastCaseB_wp hlit_lt hcnt12 hw0 hw1 hlen hlay hlit2p1 hcnt_tr hoff_pos hsz
                hget_sz hend_eq hm (hJ3 () m rfl) hQ
            · intro JB hJB
              c0_split
              · have hend_c_le : wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat +
                    cnt.toNat ≤ s.core.wlen := by omega
                clear hc; c0_to_group
                · have hs0 :
                      s.core.wstk[wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat]? =
                        some 0xFFFFFFFF#32 := by
                    rw [List.getElem?_eq_getElem (by omega)]; congr 1
                    have hget : s.core.wstk[wOff s.core.wvec lit.toNat +
                        wSz s.core.wvec lit.toNat]'(by omega) =
                        s.core.wstk[(off32.setWidth 64 + sz32.setWidth 64).toNat]'(by omega) := by
                      congr 1; exact hend_eq.symm
                    rw [hget]; exact hc
                  clear hc
                  refine wp_join_group (fun _ mW => (cnt.toNat = 2 →
                    s.core.wstk[wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat + 1]? =
                      some 0xFFFFFFFF#32) ∧ m = mW) ?_ ?_
                  · rintro _ _ mW ⟨hs1, hmW⟩; subst mW
                    have hdisjC := wpush_sentinel_disjoint hlay hlit_lt hcnt12 hs0 hs1
                    c0_to_group
                    refine wp_join_group (fun _ mW2 =>
                      ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
                      (∀ idx, idx ≠ wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat →
                        (cnt.toNat = 2 →
                          idx ≠ wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat + 1) →
                        wstkW[idx]? = s.core.wstk[idx]?) ∧
                      wstkW[wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat]? = some w0 ∧
                      (cnt.toNat = 2 →
                        wstkW[wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat + 1]? =
                          some w1) ∧
                      (FullMem c { s with core := { s.core with wstk := wstkW } } ⋆ R) mW2) ?_ ?_
                    · rintro _ _ mW2 ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW2⟩
                      have hsz_new : (sz32 + cnt).toNat = wSz s.core.wvec lit.toNat + cnt.toNat :=
                        by rw [BitVec.toNat_add, hsz]; omega
                      have hod := wvec_set_odd_u (wvec := s.core.wvec) (l := lit.toNat)
                        (v := sz32 + (cnt.setWidth 64).setWidth 32) (by omega)
                      have hsz_tr : (sz32 + (cnt.setWidth 64).setWidth 32).toNat =
                          wSz s.core.wvec lit.toNat + cnt.toNat := by
                        rw [hcnt_tr]; exact hsz_new
                      have hfin := wpush_finalize (s := s) (s2 := s)
                        (lit := lit.toNat) (cnt := cnt.toNat) (dst := wOff s.core.wvec lit.toNat)
                        (wlen' := s.core.wlen)
                        (wvec' := s.core.wvec.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
                          (sz32 + (cnt.setWidth 64).setWidth 32))
                        (wstk' := wstkW) (wsort' := s.scratch.wsort)
                        hlay (watchPresAll_refl s) hlit_lt hcnt12 hw0 hw1 (Nat.le_refl _) hoff_pos
                        (by omega)
                        (fun j hj hne => by
                          rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
                        (by rw [wOff, hlit2p1, (hod lit.toNat).1])
                        (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_tr])
                        (fun j hj hne hszj => hdisjC j hj hne hszj)
                        (fun j hj hne k hk => by
                          have hd := hdisjC j hj hne (by change 0 < wSz s.core.wvec j; omega)
                          change wOff s.core.wvec j + wSz s.core.wvec j ≤
                              wOff s.core.wvec lit.toNat ∨
                            wOff s.core.wvec lit.toNat +
                              (wSz s.core.wvec lit.toNat + cnt.toNat) ≤ wOff s.core.wvec j at hd
                          exact hpreW _ (by rcases hd with hd | hd <;> omega)
                            (fun _ => by rcases hd with hd | hd <;> omega))
                        (fun k hk => hpreW _ (by omega) (fun _ => by omega))
                        hat0W hat1W
                      c0_usteps
                      · rw [hget_sz] at hm
                        exact hQ true _ wstkW s.core.wlen (s.core.wusable - cnt.setWidth 64)
                          s.scratch.wsort _
                          { core_ok := { hco with wvec_len := by rw [List.length_set, hwvl],
                                                  wstk_len_arr := hwsW, wlen_le := hwle }
                            scratch_ok := hlen.scratch_ok }
                          (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                            (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
                          (fun h => by cases h) hm
                      · rw [hget_sz] at hm
                        exact hQ true _ wstkW s.core.wlen s.core.wusable s.scratch.wsort _
                          { core_ok := { hco with wvec_len := by rw [List.length_set, hwvl],
                                                  wstk_len_arr := hwsW, wlen_le := hwle }
                            scratch_ok := hlen.scratch_ok }
                          (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                            (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
                          (fun h => by cases h) hm
                    · intro JW hJW; clear hQ
                      have hend_p1 : ((off32.setWidth 64 + sz32.setWidth 64) + 1).toNat =
                          wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat + 1 := by
                        rw [BitVec.toNat_add, hend_eq]; simp; omega
                      c0_split
                      · have hc2 : cnt.toNat = 2 := by
                          have := bv64_eq_nat 2 (by decide) hc
                          rw [zext_toNat _ (by decide)] at this; exact this
                        c0_usteps
                        refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl],
                          fun idx hne0 hne1 => by
                            rw [hend_p1, hend_eq, List.getElem?_set_ne (by have := hne1 hc2; omega),
                              List.getElem?_set_ne (by omega)],
                          by rw [hend_p1, hend_eq, List.getElem?_set_ne (by omega),
                            List.getElem?_set_self (by omega)],
                          fun _ => by
                            rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)],
                          hm⟩
                      · c0_usteps
                        have hne2 : cnt.toNat ≠ 2 := by
                          have := bv64_ne_nat 2 (by decide) hc
                          rw [zext_toNat _ (by decide)] at this; exact this
                        refine hJW _ _ ⟨_, by rw [List.length_set, hwsl],
                          fun idx hne0 _ => by rw [hend_eq, List.getElem?_set_ne (by omega)],
                          by rw [hend_eq, List.getElem?_set_self (by omega)],
                          fun hc2 => absurd hc2 hne2, hm⟩
                  · intro Jc2 hJc2; c0_split
                    · c0_usteps
                      exact hJc2 _ _ ⟨fun hc2 => by
                        have := bv64_eq_nat 1 (by decide) hc
                        rw [zext_toNat _ (by decide)] at this; omega, rfl⟩
                    · have hc2 : cnt.toNat = 2 := by
                        have := bv64_ne_nat 1 (by decide) hc
                        rw [zext_toNat _ (by decide)] at this; omega
                      clear hc
                      c0_usteps
                      · exact hJc2 _ _ ⟨fun _ => by
                          rw [List.getElem?_eq_getElem (by omega)]; congr 1
                          have hidx' : (off32.toNat + sz32.toNat + 1) % 2 ^ 64 =
                              wOff s.core.wvec lit.toNat + wSz s.core.wvec lit.toNat + 1 := by
                            omega
                          have hget : s.core.wstk[wOff s.core.wvec lit.toNat +
                              wSz s.core.wvec lit.toNat + 1]'(by omega) =
                              s.core.wstk[(off32.toNat + sz32.toNat + 1) % 2 ^ 64]'(by omega) := by
                            congr 1; exact hidx'.symm
                          rw [hget]; exact hc, rfl⟩
                      · exact hJB () m rfl
                · exact hJB () m rfl
              · c0_usteps; exact hJB () m rfl
          · have hend0 : wOff s.core.wvec lit.toNat = 0 ∧ wSz s.core.wvec lit.toNat = 0 := by
              have hnot : ¬ (0 < (off32.toNat + sz32.toNat) % 2 ^ 64) := hc
              omega
            clear hc
            exact s8FastCaseA_wp hlit_lt hcnt12 hw0 hw1 hw_pos hend0.2 hlen hlay hlit2 hlit2p1
              hcnt_tr hm (hJ3 () m rfl) hQ
        · intro JF hJF; clear hQ
          c0_split
          · c0_usteps; exact hJF () m ⟨hw1_pos, rfl⟩
          · c0_split
            · c0_usteps; exact hJF () m ⟨hw1_pos, rfl⟩
            · c0_usteps; exact hJS () m rfl
      · c0_usteps; exact hJS () m rfl

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
