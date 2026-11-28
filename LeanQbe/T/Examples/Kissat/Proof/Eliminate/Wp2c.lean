/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp2b
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
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
# Kissat BVE `Func.wp` Helpers — Part 2c (`Wp2c`)

Modular sub-block `wp` lemmas for `full_bve_var_m7_wp` (`wp_weaken_seq`, `wp_fit_defrag`,
`wp_bve_var_commit`, `wp_bve_var_pure`, `wp_bve_var_rlen1`, `wp_bve_var_copy_loop`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Eliminate.EliminateTactics

open scoped FullArenaTactics
open scoped EliminateTactics

public section

theorem wp_join_fwd {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : Tup Val ts → Mem 64 → Prop)
    (he : ∀ (J : Cont ts), (∀ xs m', P xs m' → J xs m') → wp Γ Q X (entry (J, ())) m)
    (hb : ∀ (J : Cont ts) xs m', P xs m' → wp Γ Q X ((bodies (J, ())).get Member.here xs) m') :
    wp Γ Q X (Expr.group bodies entry) m :=
  wp_join_group P hb he

theorem wp_mux32 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[i32]] → Blocks Val Cont rs [[i32]]}
    {c : Bool} {a b : BitVec 32}
    (hb : ∀ (J : Cont [i32]) (x : BitVec 32), x = (if c then a else b) →
      wp Γ Q X ((bodies (J, ())).get Member.here (x, ())) m) :
    wp Γ Q X (Expr.group bodies fun Js =>
      Expr.jnz (Arg.var c) (Expr.jump Js.fst (Arg.imm a, ()))
        (Expr.jump Js.fst (Arg.imm b, ()))) m := by
  refine wp_join_fwd (fun xs m' => xs = ((if c then a else b), ()) ∧ m' = m) ?_ ?_
  · intro J hJ; elim_steps_nogrp
    · exact hJ _ m ⟨by simp [‹c = true›], rfl⟩
    · exact hJ _ m ⟨by cases c <;> simp_all, rfl⟩
  · rintro J ⟨x, ⟨⟩⟩ m' ⟨heq, rfl⟩
    cases heq; exact hb J _ rfl

theorem wp_loop_fwd {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : Nat → Tup Val ts → Mem 64 → Prop)
    (he : ∀ (J : Cont ts), (∀ (n : Nat) (xs : Tup Val ts) (m : Mem 64), Inv n xs m → J xs m) →
      wp Γ Q X (entry (J, ())) m)
    (hb : ∀ (J : Cont ts) (n : Nat) (xs : Tup Val ts) (m : Mem 64),
      Inv n xs m →
      (∀ (n' : Nat) (ys : Tup Val ts) (m' : Mem 64), n' < n → Inv n' ys m' → J ys m') →
      wp Γ Q X ((bodies (J, ())).get Member.here xs) m) :
    wp Γ Q X (Expr.group bodies entry) m := by
  have hbt : bodies = fun Js =>
      Blocks.cons ((bodies (Js.fst, ())).get Member.here) Blocks.nil := by
    funext ⟨J, ⟨⟩⟩; cases h : bodies (J, ()) with | cons b bs => cases bs; rfl
  have het : entry = fun Js => entry (Js.fst, ()) := by
    funext ⟨J, ⟨⟩⟩; rfl
  rw [hbt, het]
  exact wp_loop (fun J xs => (bodies (J, ())).get Member.here xs) (fun J => entry (J, ())) Inv
    (fun J n xs m hJ hI => hb J n xs m hI hJ) he

theorem bve_loops_resolve_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start sj sr : FullState} {m8 : Bool} {v np nn : BitVec 32}
    {rp r_cnt r_cnt' w_est w_est' res_sz res_sz' : BitVec 64} {fit fit' : Bool}
    {mj mr : Mem 64} {R : Mem 64 → Prop}
    (hinv : BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt w_est fit res_sz sj mj R)
    (hdw : FullDenseInvW c F0 F_cur sr)
    (hcv : sr.core.cur_vars = sj.core.cur_vars)
    (hfl : sr.core.fuel.toNat ≤ sj.core.fuel.toNat)
    (har : sr.core.arena = sj.core.arena) (hal : sr.core.arena_len = sj.core.arena_len)
    (hscr : sr.scratch = sj.scratch)
    (hm : (FullMem c sr ⋆ R) mr) :
    BveVarLoopsInv c F0 F_cur s_start m8 v np nn rp r_cnt' w_est' fit' res_sz' sr mr R :=
  ⟨hdw, by simpa [TmkZero, hscr, hcv] using hinv.2.1, hcv.trans hinv.2.2.1,
    Nat.le_trans hfl hinv.2.2.2.1,
    (by simpa using bve_entries_congr hcv har hal (off := 0) (fun _ _ => by rw [hscr])
          (fun i hi => by simpa using hinv.2.2.2.2.1 i hi)),
    bve_entries_congr hcv har hal (off := bveOccLim m8) (fun _ _ => by rw [hscr])
      hinv.2.2.2.2.2.1,
    hinv.2.2.2.2.2.2.1, hinv.2.2.2.2.2.2.2.1,
    bve_resBuf_congr hinv.2.2.2.2.2.2.2.2.1 hcv hinv.2.2.2.2.2.2.1
      (fun _ _ _ => by rw [hscr]), hm⟩

theorem bve_ret_q {c : FullCfg} {F0 : CNF Nat} {s0 s' : FullState} {m' : Mem 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {r : BitVec 64}
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hp : FullDenseInv c F0 s' ∧ TmkZero s' ∧ s0.core.cur_vars ≤ s'.core.cur_vars ∧
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
      (r = 20#64 → F0.Unsat))
    (hm : (FullMem c s' ⋆ R) m') : Q (r, ()) m' :=
  hQ r s' m' hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hm

theorem wp_weaken_seq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m : Mem 64} {R : Mem 64 → Prop}
    {rp : BitVec 64} {m8 : Bool}
    {f1 f2 : Sym} {h : BitVec 64}
    {lit1 cnt1 lit2 cnt2 : BitVec 32} {aoff1 aoff2 : Arg Val i32}
    {off1 off2 : Nat}
    {bodies : Tup Cont [[Ty.bool]] → Blocks Val Cont rs [[Ty.bool]]}
    (hf1 : Γ.Has f1 Spec.fullBveWeakenTmkSpec)
    (hf2 : Γ.Has f2 Spec.fullBveWeakenTmkSpec)
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hro : bveROff m8 ≤ rp.toNat) (hm : (FullMem c s ⋆ R) m)
    (hrb : FullResBufOkW F_cur s rp.toNat (bveROff m8))
    (hlit1 : lit1.toNat < 2 * s.core.cur_vars)
    (hoff1 : aoff1.val.toNat = off1) (hbd1 : off1 + cnt1.toNat ≤ c.scratch_cap)
    (hwk1 : ∀ i < cnt1.toNat, FullBveWeakItemOk s.core (s.scratch.scratch_buf[off1 + i]?.getD 0#32))
    (hlit2 : lit2.toNat < 2 * s.core.cur_vars)
    (hoff2 : aoff2.val.toNat = off2) (hbd2 : off2 + cnt2.toNat ≤ c.scratch_cap)
    (hwk2 : ∀ i < cnt2.toNat, FullBveWeakItemOk s.core (s.scratch.scratch_buf[off2 + i]?.getD 0#32))
    (hk : ∀ (J : Cont [Ty.bool]) (ok : Bool) (sw : FullState) (mw : Mem 64),
      FullDenseInvW c F0 F_cur sw → TmkZero sw →
      sw.core.cur_vars = s_start.core.cur_vars →
      sw.core.fuel.toNat ≤ s_start.core.fuel.toNat →
      FullResBufOkW F_cur sw rp.toNat (bveROff m8) →
      (FullMem c sw ⋆ R) mw →
      wp Γ Q X ((bodies (J, ())).get Member.here (ok, ())) mw) :
    wp Γ Q X (Expr.group bodies fun Js =>
      Expr.call (as := [i64, i32, i32, i32]) (bs := [Ty.bool]) f1
        (Arg.var h, Arg.var lit1, aoff1, Arg.var cnt1, ()) fun p1 =>
          Expr.jnz (Arg.var p1.fst)
            (Expr.call (as := [i64, i32, i32, i32]) (bs := [Ty.bool]) f2
              (Arg.var h, Arg.var lit2, aoff2, Arg.var cnt2, ()) fun p2 =>
                Expr.jnz (Arg.var p2.fst) (Expr.jump Js.fst (Arg.imm true, ()))
                  (Expr.jump Js.fst (Arg.imm false, ())))
            (Expr.jump Js.fst (Arg.imm false, ()))) m := by
  refine wp_join_fwd (fun xs mw => ∃ ok sw, xs = (ok, ()) ∧
      FullDenseInvW c F0 F_cur sw ∧ TmkZero sw ∧
      sw.core.cur_vars = s_start.core.cur_vars ∧ sw.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
      FullResBufOkW F_cur sw rp.toNat (bveROff m8) ∧ (FullMem c sw ⋆ R) mw) ?_ ?_
  · intro J hJ
    refine wp_call_of_spec _ _ (hf1 _ _ _ _ ?_)
    refine ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hlit1, (by rw [hoff1]; exact hbd1),
      (by simpa [hoff1] using hwk1), hm, ?_⟩
    rintro ok1 s1 m1 hdw1 htmk1 hcv1 hfl1 hscr1 hrefs1 hm1
    have hrb1 := bve_resBuf_congr hrb hcv1 hro (fun _ _ _ => by rw [hscr1])
    have hwk2' := bve_weak_items_congr hcv1 hrefs1 hscr1 hwk2
    elim_steps_nogrp
    · refine wp_call_of_spec _ _ (hf2 _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, s1, R, hh, hdw1, htmk1, (by rw [hcv1]; exact hlit2),
        (by rw [hoff2]; exact hbd2), (by simpa [hoff2] using hwk2'), hm1, ?_⟩
      rintro ok2 s2 m2 hdw2 htmk2 hcv2 hfl2 hscr2 _ hm2
      have hrb2 := bve_resBuf_congr hrb1 hcv2 hro (fun _ _ _ => by rw [hscr2])
      elim_steps_nogrp
      · exact hJ (true, ()) m2 ⟨true, s2, rfl, hdw2, htmk2, hcv2.trans (hcv1.trans hcv),
          by rw [hfl2, hfl1]; exact hfl, hrb2, hm2⟩
      · exact hJ (false, ()) m2 ⟨false, s2, rfl, hdw2, htmk2, hcv2.trans (hcv1.trans hcv),
          by rw [hfl2, hfl1]; exact hfl, hrb2, hm2⟩
    · exact hJ (false, ()) m1 ⟨false, s1, rfl, hdw1, htmk1, hcv1.trans hcv,
        by rw [hfl1]; exact hfl, hrb1, hm1⟩
  · rintro J ⟨ok, ⟨⟩⟩ mw ⟨ok', sw, heq, hdw', htmk', hcv', hfl', hrb', hm'⟩
    cases heq
    exact hk J ok sw mw hdw' htmk' hcv' hfl' hrb' hm'

theorem wp_fit_defrag {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_start s : FullState} {m : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v np nn : BitVec 32} {rp ar_need w_need acap wcap : BitVec 64}
    {h : BitVec 64} {fit_prev : Bool}
    {bodies : Tup Cont [[Ty.bool]] → Blocks Val Cont rs [[Ty.bool]]}
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hcv : s.core.cur_vars = s_start.core.cur_vars)
    (hfl : s.core.fuel.toNat ≤ s_start.core.fuel.toNat)
    (hro : bveROff m8 ≤ rp.toNat) (hm : (FullMem c s ⋆ R) m)
    (hacap : acap = BitVec.ofNat 64 c.arena_cap) (hwcap : wcap = BitVec.ofNat 64 c.wcap)
    (hent_p : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32))
    (hrb : FullResBufOkW F_cur s rp.toNat (bveROff m8))
    (hk : ∀ (J : Cont [Ty.bool]) (fit' : Bool) (sf : FullState) (mf : Mem 64),
      FullDenseInvW c F0 F_cur sf → TmkZero sf →
      sf.core.cur_vars = s_start.core.cur_vars → sf.core.fuel.toNat ≤ s_start.core.fuel.toNat →
      (∀ i < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
        (sf.scratch.scratch_buf[i]?.getD 0#32)) →
      (∀ j < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
        (sf.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) →
      FullResBufOkW F_cur sf rp.toNat (bveROff m8) → (FullMem c sf ⋆ R) mf →
      wp Γ Q X ((bodies (J, ())).get Member.here (fit', ())) mf) :
    wp Γ Q X (Expr.group bodies fun Js =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 48, ())) fun p49 =>
      Expr.load i64 (Arg.var p49.fst) fun ld_al =>
      Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var acap, Arg.var ld_al, ())) fun p50 =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
        (Arg.var ar_need, Arg.var p50.fst, ())) fun p51 =>
      Expr.jnz (Arg.var p51.fst) (Expr.jump Js.fst (Arg.imm false, ()))
        (Expr.group (fun (_Js_1 : Tup Cont [[Ty.bool]]) =>
            Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js2 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 56, ())) fun p52 =>
          Expr.load i64 (Arg.var p52.fst) fun ld_wl =>
          Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var wcap, Arg.var ld_wl, ())) fun p53 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
            (Arg.var w_need, Arg.var p53.fst, ())) fun p54 =>
          Expr.jnz (Arg.var p54.fst)
            (Expr.group (fun (_Js_2 : Tup Cont [[]]) => Blocks.cons (fun _ =>
              Expr.group (fun (_Js_3 : Tup Cont [[Ty.bool]]) => Blocks.cons
                  (fun p => Expr.jump Js2.fst (Arg.var p.fst, ())) Blocks.nil) fun Js3 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 56, ())) fun pw1 =>
                Expr.load i64 (Arg.var pw1.fst) fun ldw2 =>
                Expr.let_ (Op.mk (OpCode.sub i64)
                  (Arg.var wcap, Arg.var ldw2, ())) fun pw2 =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                  (Arg.var w_need, Arg.var pw2.fst, ())) fun pw3 =>
                Expr.jnz (Arg.var pw3.fst) (Expr.jump Js3.fst (Arg.imm false, ()))
                  (Expr.jump Js3.fst (Arg.var fit_prev, ()))) Blocks.nil) fun Js_d =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 464, ())) fun p55 =>
              Expr.load i64 (Arg.var p55.fst) fun ldwu =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                (Arg.var ldwu, Arg.imm 0, ())) fun p56 =>
              Expr.jnz (Arg.var p56.fst)
                (Expr.call (as := [i64]) (bs := []) "full_wstack_defrag" (Arg.var h, ()) fun _ =>
                  Expr.jump Js_d.fst ())
                (Expr.jump Js_d.fst ()))
            (Expr.jump Js2.fst (Arg.var fit_prev, ())))) m := by
  subst hh hacap hwcap
  refine wp_join_fwd (fun xs mf => ∃ sf : FullState,
      FullDenseInvW c F0 F_cur sf ∧ TmkZero sf ∧
      sf.core.cur_vars = s_start.core.cur_vars ∧ sf.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
        (sf.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
        (sf.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
      FullResBufOkW F_cur sf rp.toNat (bveROff m8) ∧ (FullMem c sf ⋆ R) mf) ?_
    (fun J xs mf ⟨sf, hdwf, htmkf, hcvf, hflf, hpf, hnf, hrbf, hmf⟩ =>
      hk J xs.1 sf mf hdwf htmkf hcvf hflf hpf hnf hrbf hmf)
  intro J_fit hJ_fit; elim_steps_nogrp
  · exact hJ_fit (false, ()) m ⟨s, hdw, htmk, hcv, hfl, hent_p, hent_n, hrb, hm⟩
  · refine wp_join_fwd (fun xs mf => ∃ sd : FullState,
        FullDenseInvW c F0 F_cur sd ∧ TmkZero sd ∧
        sd.core.cur_vars = s_start.core.cur_vars ∧ sd.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
        (∀ i < np.toNat, FullBveEntryOkW F_cur sd (2 * v.toNat)
          (sd.scratch.scratch_buf[i]?.getD 0#32)) ∧
        (∀ j < nn.toNat, FullBveEntryOkW F_cur sd (2 * v.toNat + 1)
          (sd.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
        FullResBufOkW F_cur sd rp.toNat (bveROff m8) ∧ (FullMem c sd ⋆ R) mf) ?_ ?_
    · intro J2 hJ2; elim_steps_nogrp
      · refine wp_join_fwd (fun _ mf => ∃ sd : FullState,
            FullDenseInvW c F0 F_cur sd ∧ TmkZero sd ∧
            sd.core.cur_vars = s_start.core.cur_vars ∧
            sd.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
            (∀ i < np.toNat, FullBveEntryOkW F_cur sd (2 * v.toNat)
              (sd.scratch.scratch_buf[i]?.getD 0#32)) ∧
            (∀ j < nn.toNat, FullBveEntryOkW F_cur sd (2 * v.toNat + 1)
              (sd.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
            FullResBufOkW F_cur sd rp.toNat (bveROff m8) ∧ (FullMem c sd ⋆ R) mf) ?_ ?_
        · intro J_d hJ_d; elim_steps_nogrp
          · refine wp_call_of_spec _ _ (hDefrag _ _ _ _ ?_)
            refine ⟨c, s, R, rfl, hdw.1, hdw.2.1.watches.layout, hm, ?_⟩
            intro wv' ws' wlen' wsort' mf _ hlok' hlay' _ hwat' hmf
            let sd0 : FullState :=
              { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
                scratch := { s.scratch with wsort := wsort' } }
            have ⟨hdw', htmk', hrb'⟩ := bve_defrag_post hdw htmk hrb hro hlok' hlay' hwat'
            elim_steps_nogrp
            exact hJ_d () mf ⟨sd0, hdw', htmk', hcv, hfl,
              (fun i hi => by
                simpa using bve_entries_congr (s := s) (s' := sd0) rfl rfl rfl (off := 0)
                  (fun _ _ => rfl) (fun i' hi' => by simpa using hent_p i' hi') i hi),
              bve_entries_congr (s := s) (s' := sd0) rfl rfl rfl (off := bveOccLim m8)
                (fun _ _ => rfl) hent_n,
              hrb', hmf⟩
          · exact hJ_d () m ⟨s, hdw, htmk, hcv, hfl, hent_p, hent_n, hrb, hm⟩
        rintro _ _ m_d ⟨sd, hdwd, htmkd, hcvd, hfld, hpd, hnd, hrbd, hmd⟩
        refine wp_join_fwd (fun xs mf => ∃ sd' : FullState,
            FullDenseInvW c F0 F_cur sd' ∧ TmkZero sd' ∧
            sd'.core.cur_vars = s_start.core.cur_vars ∧
            sd'.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
            (∀ i < np.toNat, FullBveEntryOkW F_cur sd' (2 * v.toNat)
              (sd'.scratch.scratch_buf[i]?.getD 0#32)) ∧
            (∀ j < nn.toNat, FullBveEntryOkW F_cur sd' (2 * v.toNat + 1)
              (sd'.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
            FullResBufOkW F_cur sd' rp.toNat (bveROff m8) ∧ (FullMem c sd' ⋆ R) mf) ?_ ?_
        · intro J3 hJ3; elim_steps_nogrp
          · exact hJ3 (false, ()) m_d ⟨sd, hdwd, htmkd, hcvd, hfld, hpd, hnd, hrbd, hmd⟩
          · exact hJ3 (fit_prev, ()) m_d ⟨sd, hdwd, htmkd, hcvd, hfld, hpd, hnd, hrbd, hmd⟩
        · rintro _ ⟨b3, ⟨⟩⟩ m_d3 ⟨sd', hdw3, htmk3, hcv3, hfl3, hp3, hn3, hrb3, hm3⟩
          elim_steps_nogrp
          exact hJ2 (b3, ()) m_d3 ⟨sd', hdw3, htmk3, hcv3, hfl3, hp3, hn3, hrb3, hm3⟩
      · exact hJ2 (fit_prev, ()) m ⟨s, hdw, htmk, hcv, hfl, hent_p, hent_n, hrb, hm⟩
    rintro _ ⟨b2, ⟨⟩⟩ mf ⟨sf, hdwf, htmkf, hcvf, hflf, hpf, hnf, hrbf, hmf⟩
    elim_steps_nogrp
    exact hJ_fit (b2, ()) mf ⟨sf, hdwf, htmkf, hcvf, hflf, hpf, hnf, hrbf, hmf⟩

theorem wp_bve_var_commit {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sw : FullState} {m_w : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v : BitVec 32} {h r_off rp : BitVec 64} {flag : BitVec 32}
    (hInactive : Γ.Has "full_set_inactive" Internal.Spec.fullSetInactiveSpec)
    (hCommit : Γ.Has "full_bve_commit_res" Spec.fullBveCommitResTmkSpec)
    (hFlush : Γ.Has "full_dense_flush_units_m7" Dense.Spec.fullDenseFlushUnitsSpec)
    (hh : h = c.hdr) (h_roff : r_off.toNat = bveROff m8)
    (hv0 : v.toNat < s0.core.cur_vars) (hdww : FullDenseInvW c F0 F_cur sw)
    (htmkw : TmkZero sw) (hcvw : sw.core.cur_vars = s0.core.cur_vars)
    (hflw : sw.core.fuel.toNat ≤ s0.core.fuel.toNat) (hro : bveROff m8 ≤ rp.toNat)
    (hsc : rp.toNat ≤ c.scratch_cap)
    (hrbw : FullResBufOkW F_cur sw rp.toNat (bveROff m8))
    (hmw : (FullMem c sw ⋆ R) m_w)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_set_inactive"
        (Arg.var h, Arg.var v, Arg.imm flag, ()) fun _ =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1088, ())) fun p1 =>
      Expr.load i64 (Arg.var p1.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p2 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1088, ())) fun p3 =>
      Expr.store (Arg.var p2.fst) (Arg.var p3.fst)
        (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "full_bve_commit_res"
          (Arg.var h, Arg.var r_off, Arg.var rp, ()) fun p =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
          (Arg.var p.fst, Arg.imm 20, ())) fun p4 =>
        Expr.jnz (Arg.var p4.fst) (Expr.ret (Arg.imm 20, ()))
          (Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
            (Arg.var p.fst, Arg.imm 1, ())) fun p5 =>
          Expr.jnz (Arg.var p5.fst)
            (Expr.call (as := [i64]) (bs := [Ty.bool]) "full_dense_flush_units_m7"
              (Arg.var h, ()) fun p6 =>
            Expr.jnz (Arg.var p6.fst) (Expr.ret (Arg.var p.fst, ()))
              (Expr.ret (Arg.imm 20, ())))
            (Expr.ret (Arg.var p.fst, ()))))) m_w := by
  subst hh
  refine wp_call_of_spec _ _ (hInactive _ _ _ _ ?_)
  refine ⟨c, sw, R, rfl, hdww.1, hmw, ?_⟩
  have hnv : ¬ (sw.core.cur_vars ≤ (Arg.var (t := i32) v).val.toNat) := by
    dsimp only [Arg.val]; omega
  rw [ite_eq_right (fun hlt => absurd hlt hnv)]
  intro fl' un' sc' mi s_i hlok_i hpr_i hm_i
  have ⟨hdwi, htmki, hrbi⟩ := bve_set_inactive_inv hdww htmkw hrbw hro hlok_i hpr_i
  elim_steps_nogrp
  have ⟨hdwb, htmkb, hrbb⟩ := bve_bveCnt_add1_inv hdwi htmki hrbi hro
  refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
  refine ⟨c, F0, F_cur, _, R, rfl, hdwb, htmkb,
    (by dsimp only [Arg.val]; rw [h_roff]; exact hro), hsc,
    (by dsimp only [Arg.val]; rw [h_roff]; exact hrbb),
    (by dsimp only [s_i]; assumption), ?_⟩
  rintro cr scr_c m_c hdw_c htmk_c hcv_c hfl_c hcr huns_c hm_c
  elim_steps_nogrp
  · have hcr20 : cr = 20#64 := ‹_›
    exact bve_ret_q hQ
      (bve_commit_ret_post hdw_c htmk_c hcvw hcv_c hflw hfl_c (Or.inr (Or.inr rfl))
        (fun _ => huns_c hcr20)) hm_c
  · have hcr1 : cr = 1#64 := ‹_›
    refine wp_call_of_spec _ _ (hFlush _ _ _ _ ?_)
    refine ⟨c, F0, F_cur, scr_c, R, rfl, hdw_c, hm_c, ?_⟩
    rintro fok s_fl m_fl hdw_fl hcv_fl _ hfl_fl _ htm_fl _ _ _ _ _ huns_fl hm_fl
    have htmk_fl : TmkZero s_fl := by simpa [TmkZero, htm_fl, hcv_fl] using htmk_c
    elim_steps_nogrp
    · have hp := bve_flush_ret_post (ok := true) hdw_fl htmk_fl hcvw hcv_c hcv_fl
        hflw hfl_c hfl_fl (fun h => by simp at h)
      rw [hcr1]
      exact bve_ret_q hQ (by simpa using hp) hm_fl
    · have hfok : fok = false := by cases fok <;> first | rfl | contradiction
      have hp := bve_flush_ret_post (ok := false) hdw_fl htmk_fl hcvw hcv_c hcv_fl
        hflw hfl_c hfl_fl (fun _ => huns_fl hfok)
      exact bve_ret_q hQ (by simpa using hp) hm_fl
  · exact bve_ret_q hQ
      (bve_commit_ret_post hdw_c htmk_c hcvw hcv_c hflw hfl_c hcr huns_c) hm_c

theorem wp_bve_var_pure {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 : FullState} {m2 : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v pl nl neg_off np nn : BitVec 32} {h : BitVec 64}
    (hWeakenUnit : Γ.Has "full_bve_weaken_unit_fid" Spec.fullBveWeakenTmkSpec)
    (hInactive : Γ.Has "full_set_inactive" Internal.Spec.fullSetInactiveSpec)
    (hh : h = c.hdr) (hv0 : v.toNat < s0.core.cur_vars)
    (hpl : pl.toNat < 2 * s0.core.cur_vars) (hnl : nl.toNat < 2 * s0.core.cur_vars)
    (hneg_off : neg_off.toNat = bveOccLim m8)
    (hnp_le : np.toNat ≤ bveOccLim m8) (hnn_le : nn.toNat ≤ bveOccLim m8)
    (h2lim : bveOccLim m8 + bveOccLim m8 ≤ c.scratch_cap)
    (hdw2 : FullDenseInvW c F0 F_cur s2) (htmk2 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars)
    (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.group (fun (_Js_oom : Tup Cont [[]]) =>
        Blocks.cons (fun _ =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 760, ())) fun p =>
          Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst) (Expr.ret (Arg.imm 2, ()))) Blocks.nil)
        fun Js_oom =>
      Expr.group (fun (_Js_n : Tup Cont [[]]) =>
        Blocks.cons (fun _ =>
          Expr.group (fun (_Js_i : Tup Cont [[]]) =>
            Blocks.cons (fun _ =>
              Expr.call (as := [i64, i32, i32]) (bs := []) "full_set_inactive"
                (Arg.var h, Arg.var v, Arg.imm 2, ()) fun _ =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1088, ())) fun p1 =>
              Expr.load i64 (Arg.var p1.fst) fun ld =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1088, ())) fun p3 =>
              Expr.store (Arg.var p2.fst) (Arg.var p3.fst)
                (Expr.ret (Arg.imm 1, ()))) Blocks.nil)
            fun Js_i =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide))
            (Arg.var nn, Arg.imm 0, ())) fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.call (as := [i64, i32, i32, i32]) (bs := [Ty.bool]) "full_bve_weaken_unit_fid"
              (Arg.var h, Arg.var nl, Arg.var neg_off, Arg.var nn, ()) fun p1 =>
            Expr.jnz (Arg.var p1.fst) (Expr.jump Js_i.fst ()) (Expr.jump Js_oom.fst ()))
            (Expr.jump Js_i.fst ())) Blocks.nil)
        fun Js_n =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide))
        (Arg.var np, Arg.imm 0, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64, i32, i32, i32]) (bs := [Ty.bool]) "full_bve_weaken_unit_fid"
          (Arg.var h, Arg.var pl, Arg.imm 0, Arg.var np, ()) fun p1 =>
        Expr.jnz (Arg.var p1.fst) (Expr.jump Js_n.fst ()) (Expr.jump Js_oom.fst ()))
        (Expr.jump Js_n.fst ())) m2 := by
  subst hh
  refine wp_join_group (fun _ m' => ∃ s_o : FullState,
      FullDenseInvW c F0 F_cur s_o ∧ TmkZero s_o ∧
      s_o.core.cur_vars = s0.core.cur_vars ∧ s_o.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c s_o ⋆ R) m') ?_ ?_
  · rintro _ _ m_o ⟨so, hdwo, htmko, hcvo, hflo, hmo⟩
    elim_steps_nogrp
    have hoom := bve_oom_post hdwo htmko hcvo hflo
    exact bve_ret_q hQ ⟨hoom.1, hoom.2.1, hoom.2.2.1, hoom.2.2.2, Or.inr (Or.inl rfl),
      fun h20 => by simp at h20⟩ ‹_›
  intro J_oom hJ_oom
  refine wp_join_fwd (fun _ m' => ∃ s_n : FullState,
      FullDenseInvW c F0 F_cur s_n ∧ TmkZero s_n ∧
      s_n.core.cur_vars = s0.core.cur_vars ∧ s_n.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (∀ j < nn.toNat, FullBveWeakItemOk s_n.core
        (s_n.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
      (FullMem c s_n ⋆ R) m') ?_ ?_
  · intro J_n hJ_n
    have hwk_n2 := bve_weak_items_of_entries (off := bveOccLim m8) hent_n2
    elim_steps_nogrp
    · refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
      have hwk_p2 := bve_weak_items_of_entries (off := 0)
        (fun i hi => by simpa using hent_p2 i hi)
      refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk2,
        (by dsimp only [Arg.val]; rw [hcv2]; exact hpl),
        (by simp [Arg.val]; omega),
        (fun i hi => by simpa [Arg.val] using hwk_p2 i hi), hm2, ?_⟩
      rintro ok1 sp1 mp1 hdw_p1 htmk_p1 hcv_p1 hfl_p1 hscr_p1 hrefs_p1 hm_p1
      have hwk_n' := bve_weak_items_congr hcv_p1 hrefs_p1 hscr_p1 hwk_n2
      elim_steps_nogrp
      · exact hJ_n () mp1 ⟨sp1, hdw_p1, htmk_p1, hcv_p1.trans hcv2,
          by rw [hfl_p1]; exact hfl2, hwk_n', hm_p1⟩
      · exact hJ_oom () mp1 ⟨sp1, hdw_p1, htmk_p1, hcv_p1.trans hcv2,
          by rw [hfl_p1]; exact hfl2, hm_p1⟩
    · exact hJ_n () m2 ⟨s2, hdw2, htmk2, hcv2, hfl2, hwk_n2, hm2⟩
  rintro _ _ m_n ⟨sn, hdwn, htmkn, hcvn, hfln, hwkn, hmn⟩
  refine wp_join_group (fun _ m' => ∃ s_i : FullState,
      FullDenseInvW c F0 F_cur s_i ∧ TmkZero s_i ∧
      s_i.core.cur_vars = s0.core.cur_vars ∧ s_i.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c s_i ⋆ R) m') ?_ ?_
  · rintro _ _ m_i ⟨si, hdwi, htmki, hcvi, hfli, hmi⟩
    refine wp_call_of_spec _ _ (hInactive _ _ _ _ ?_)
    refine ⟨c, si, R, rfl, hdwi.1, hmi, ?_⟩
    have hnv : ¬ (si.core.cur_vars ≤ (Arg.var (t := i32) v).val.toNat) := by
      dsimp only [Arg.val]; omega
    rw [ite_eq_right (fun hlt => absurd hlt hnv)]
    intro fl' un' sc' mi s_i hlok_i hpr_i hm_i
    have ⟨hdw_f, htmk_f, _⟩ :=
      bve_set_inactive_inv hdwi htmki FullResBufOkW.nil (Nat.le_refl 0) hlok_i hpr_i
    elim_steps_nogrp
    have ⟨hdwb, htmkb, _⟩ :=
      bve_bveCnt_add1_inv hdw_f htmk_f FullResBufOkW.nil (Nat.le_refl 0)
    refine bve_ret_q hQ ⟨hdwb.toDense, htmkb, (by dsimp only [s_i]; omega), hfli, Or.inl rfl,
      fun h20 => by simp at h20⟩ ?_
    dsimp only [s_i]; assumption
  · intro J_i hJ_i; elim_steps_nogrp
    · refine wp_call_of_spec _ _ (hWeakenUnit _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, sn, R, rfl, hdwn, htmkn,
        (by dsimp only [Arg.val]; rw [hcvn]; exact hnl),
        (by dsimp only [Arg.val]; rw [hneg_off]; omega),
        (by simpa [hneg_off] using hwkn), hmn, ?_⟩
      rintro ok2 sn2 mn2 hdw_n2 htmk_n2 hcv_n2 hfl_n2 _ _ hm_n2
      elim_steps_nogrp
      · exact hJ_i () mn2 ⟨sn2, hdw_n2, htmk_n2, hcv_n2.trans hcvn,
          by rw [hfl_n2]; exact hfln, hm_n2⟩
      · exact hJ_oom () mn2 ⟨sn2, hdw_n2, htmk_n2, hcv_n2.trans hcvn,
          by rw [hfl_n2]; exact hfln, hm_n2⟩
    · exact hJ_i () m_n ⟨sn, hdwn, htmkn, hcvn, hfln, hmn⟩

private theorem bv8_sext32_toInt (x : BitVec 8) : (BitVec.signExtend 32 x).toInt = x.toInt := by
  rw [BitVec.toInt_signExtend]
  simp only [show min 32 8 = 8 by decide, Nat.reducePow]
  have := x.le_toInt; have := x.toInt_lt
  rw [Int.bmod_eq_of_le] <;> omega

theorem wp_bve_var_rlen1 {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sj sr : FullState} {mj mr : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v np nn : BitVec 32}
    {h p_u pVals n2 rpj r_cntj w_estj res_szj res_sz' : BitVec 64}
    {bodies : Tup Cont [[]] → Blocks Val Cont [i64] [[]]}
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    (hh : h = c.hdr) (hp_u : p_u = c.pTmp + BitVec.ofNat 64 0 * 4) (hpVals : pVals = c.pVals)
    (hinv_j : BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_szj sj mj R)
    (hdw_sr : FullDenseInvW c F0 F_cur sr)
    (hcv_r : sr.core.cur_vars = sj.core.cur_vars)
    (hfl_r : sr.core.fuel.toNat ≤ sj.core.fuel.toNat)
    (har_r : sr.core.arena = sj.core.arena) (hal_r : sr.core.arena_len = sj.core.arena_len)
    (hscr_r : sr.scratch = sj.scratch) (hm_r : (FullMem c sr ⋆ R) mr)
    (hbd_r : ∀ k < 1, (sr.core.tmp[k]?.getD 0#32).toNat < 2 * sr.core.cur_vars)
    (hent_r : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((sr.core.tmp.take 1).map BitVec.toNat)))
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hk : ∀ (J22 : Cont []) (sa : FullState) (ma : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sa ma R →
      wp Γ Q X ((bodies (J22, ())).get Member.here ()) ma) :
    wp Γ Q X
      (Expr.load i32 (Arg.var p_u) fun ld_u =>
       Expr.group bodies fun Js22 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_u, ())) fun p3 =>
       Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
         (Arg.var p3.fst, Arg.var n2, ())) fun p4 =>
       Expr.jnz (Arg.var p4.fst)
         (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_u, ())) fun p5 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pVals, Arg.var p5.fst, ())) fun p6 =>
          Expr.load i8 (Arg.var p6.fst) fun ld_v =>
          Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p7 =>
          Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p8 =>
          Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p7.fst, ())) fun p9 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.slt i32 Ty.bool (by decide))
            (Arg.var p8.fst, Arg.var p9.fst, ())) fun p10 =>
          Expr.jnz (Arg.var p10.fst)
            (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1144, ())) fun p11 =>
             Expr.store (t := i64) (Arg.var res_sz') (Arg.var p11.fst)
               (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun p12 =>
                Expr.store (t := i64) (Arg.imm 1) (Arg.var p12.fst)
                  (Expr.ret (Arg.imm 20, ()))))
            (Expr.group (fun (_Js23 : Tup Cont [[]]) =>
               Blocks.cons (fun _ => Expr.jump Js22.fst ()) Blocks.nil) fun Js23 =>
             Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p13 =>
             Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p14 =>
             Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p13.fst, ())) fun p15 =>
             Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 Ty.bool (by decide))
               (Arg.var p14.fst, Arg.var p15.fst, ())) fun p16 =>
             Expr.jnz (Arg.var p16.fst)
               (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
                 (Arg.var h, Arg.var ld_u, Arg.imm 4294967295, Arg.imm 0, ()) fun _ =>
                Expr.jump Js23.fst ())
               (Expr.jump Js23.fst ())))
         (Expr.jump Js22.fst ())) mr := by
  subst hh hp_u hpVals
  have htl_pos : 1 ≤ sr.core.tmp.length := by
    rw [hdw_sr.1.core_ok.tmp_len_arr]
    have := hdw_sr.1.core_ok.cur_vars_le; have := hbd_r 0 (by omega); omega
  have hinv_r : BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sr mr R :=
    bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r
  elim_steps_nogrp
  refine wp_join_fwd (fun _ m' => ∃ sa,
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sa m' R) ?_ ?_
  · intro J22 hJ22; elim_steps_nogrp
    · have h0_lt : sr.core.tmp[0].toNat < 2 * sr.core.cur_vars := by
        have hlt := hbd_r 0 (by omega)
        simpa [List.getElem?_eq_getElem htl_pos] using hlt
      have hvl : sr.core.tmp[0].toNat < sr.core.vals.length := by
        rw [hdw_sr.1.core_ok.vals_len]
        have := hdw_sr.1.core_ok.cur_vars_le; omega
      have hul_v :
          (BitVec.setWidth 64 sr.core.tmp[(BitVec.ofNat 64 0).toNat]).toNat <
            sr.core.vals.length := by
        rw [hdw_sr.1.core_ok.vals_len, BitVec.toNat_setWidth]
        have := hdw_sr.1.core_ok.cur_vars_le
        have hcv31 := bve_cur_vars_lt31 hdw_sr.1
        change sr.core.tmp[0].toNat % 2 ^ 64 < 2 * c.max_vars
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      elim_steps_nogrp
      · have hneg : (sr.core.vals[(sr.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8).slt 0#8 = true := by
          have hge : sr.core.tmp[0]?.getD 0#32 = sr.core.tmp[0] := by
            simp [List.getElem?_eq_getElem htl_pos]
          rw [hge, List.getElem?_eq_getElem hvl, Option.getD_some]
          have hslt : (BitVec.signExtend 32 sr.core.vals[sr.core.tmp[0].toNat]).slt
              (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true := ‹_›
          rw [BitVec.slt, decide_eq_true_eq, bv8_sext32_toInt, bv8_sext32_toInt] at hslt
          rw [BitVec.slt, decide_eq_true_eq]
          have h0 : (BitVec.truncate 8 0#32).toInt = (0#8).toInt := by decide
          rwa [h0] at hslt
        have hcf := bve_rlen1_conflict_ret20 res_sz' hdw_sr
          (by simpa [TmkZero, hscr_r, hcv_r] using hinv_j.2.1)
          (hcv_r.trans hinv_j.2.2.1)
          (Nat.le_trans hfl_r hinv_j.2.2.2.1) (hbd_r 0 (by omega))
          (List.ne_nil_of_length_pos htl_pos) hent_r hneg
        exact bve_ret_q hQ ⟨hcf.1, hcf.2.1, hcf.2.2.1, hcf.2.2.2.1,
          Or.inr (Or.inr rfl), fun _ => hcf.2.2.2.2⟩ ‹_›
      · refine wp_join_fwd (fun _ m' => ∃ sa,
            BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sa m' R) ?_ ?_
        · intro J23 hJ23; elim_steps_nogrp
          · refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
            refine ⟨c, sr, R, rfl, hdw_sr.1, hm_r, ?_⟩
            have hge : sr.core.tmp[0]?.getD 0#32 = sr.core.tmp[0] := by
              simp [List.getElem?_eq_getElem htl_pos]
            have hv_eq0 : sr.core.vals[sr.core.tmp[0].toNat] = 0#8 := by
              have heq : BitVec.signExtend 32 sr.core.vals[sr.core.tmp[0].toNat] =
                  BitVec.signExtend 32 (BitVec.truncate 8 0#32) := ‹_›
              apply BitVec.eq_of_toInt_eq
              have hi := congrArg BitVec.toInt heq
              rw [bv8_sext32_toInt, bv8_sext32_toInt] at hi
              have h0 : (BitVec.truncate 8 0#32).toInt = (0#8).toInt := by decide
              rwa [h0] at hi
            have hul_v0 : sr.core.vals[(sr.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 0#8 := by
              rw [hge, List.getElem?_eq_getElem hvl, Option.getD_some]; exact hv_eq0
            by_cases hte : c.max_vars ≤ sr.core.trail_end
            · split
              · elim_steps_nogrp; exact hJ23 () mr ⟨sr, hinv_r⟩
              · rename_i hnc; exact absurd (Or.inr (Or.inl hte)) hnc
            · split
              · rename_i hc_if
                have hcond : ¬ (sr.core.cur_vars ≤ sr.core.tmp[0].toNat / 2 ∨
                    c.max_vars ≤ sr.core.trail_end ∨
                    sr.core.vals[sr.core.tmp[0].toNat]?.getD 0#8 ≠ 0#8) := by
                  rw [List.getElem?_eq_getElem hvl, Option.getD_some, hv_eq0]
                  simp [hte]; omega
                exact absurd hc_if hcond
              · intro v_l rsn_l unfl_l fl' un' ph' m_a hfl_l hph_l s_a hm_a
                elim_steps_nogrp
                have hres_a := bve_loops_rlen1_assign hinv_r htl_pos
                  (hbd_r 0 (by omega)) hul_v0 hent_r hfl_l hph_l
                  (by dsimp only [s_a, v_l, rsn_l, unfl_l, Arg.val] at hm_a; simpa [hge] using hm_a)
                exact hJ23 () m_a ⟨_, hres_a⟩
          · exact hJ23 () mr ⟨sr, hinv_r⟩
        · rintro _ _ ma ⟨sa, hinv_a⟩; elim_steps_nogrp
          exact hJ22 () ma ⟨sa, hinv_a⟩
    · exact hJ22 () mr ⟨sr, hinv_r⟩
  · rintro J22 _ ma ⟨sa, hinv_a⟩
    exact hk J22 sa ma hinv_a

theorem wp_bve_var_copy_loop {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sr : FullState} {mr mk0 : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v np nn j : BitVec 32}
    {pTmp pScr pWvec n2 rpj r_cntj r_cnt' w_estj res_sz' tl_bv : BitVec 64}
    {fit_a : Bool} {tl_r : Nat}
    {J_a : Cont [i64, i64, i64, Ty.bool, i32]}
    (hpTmp : pTmp = c.pTmp) (hpScr : pScr = c.pScratchBuf) (hpWvec : pWvec = c.pWvec)
    (htl_bv : tl_bv = BitVec.ofNat 64 tl_r) (htl_lt32 : tl_r < 2 ^ 32)
    (htl_le : tl_r ≤ sr.core.cur_vars)
    (hr_cnt' : r_cnt' = r_cntj + 1#64) (hfit_a : fit_a = true)
    (hnp_le : np.toNat ≤ bveOccLim m8) (hnn_le : nn.toNat ≤ bveOccLim m8)
    (hinv_r : BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sr mr R)
    (hbd_rp : rpj.toNat + 1 + tl_r ≤ c.scratch_cap)
    (hbd_r : ∀ k < tl_r, (sr.core.tmp[k]?.getD 0#32).toNat < 2 * sr.core.cur_vars)
    (hnd_r : ((sr.core.tmp.take tl_r).map (fun x => x.toNat / 2)).Nodup)
    (hent_r : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((sr.core.tmp.take tl_r).map BitVec.toNat)))
    (hmk0 : (FullMem c (FullState.mk sr.core { sr.scratch with
        scratch_buf := sr.scratch.scratch_buf.set rpj.toNat (BitVec.ofNat 32 tl_r) }) ⋆ R) mk0)
    (hJ_a : ∀ (w_estk : BitVec 64) (s_done : FullState) (mk : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn (rpj + 1#64 + BitVec.ofNat 64 tl_r)
        (r_cntj + 1#64) w_estk true res_sz' s_done mk R →
      J_a (rpj + 1#64 + BitVec.ofNat 64 tl_r, r_cntj + 1#64, w_estk, true, j, ()) mk) :
    wp Γ Q X
      (Expr.group (fun (Js : Tup Cont [[i64, i32]]) =>
        Blocks.cons (fun pk =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.snd.fst, ())) fun p0 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
            (Arg.var p0.fst, Arg.var tl_bv, ())) fun p1 =>
          Expr.jnz (Arg.var p1.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.snd.fst, ())) fun p2 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p2.fst, Arg.imm 4, ())) fun p3 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pTmp, Arg.var p3.fst, ())) fun p4 =>
             Expr.load i32 (Arg.var p4.fst) fun ld_l =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var rpj, Arg.imm 1, ())) fun p5 =>
             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.snd.fst, ())) fun p6 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p5.fst, Arg.var p6.fst, ())) fun p7 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p7.fst, Arg.imm 4, ())) fun p8 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pScr, Arg.var p8.fst, ())) fun p9 =>
             Expr.store (t := i32) (Arg.var ld_l) (Arg.var p9.fst)
               (Expr.group (fun (_Jkn : Tup Cont [[i64]]) =>
                  Blocks.cons (fun pw =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pk.snd.fst, Arg.imm 1, ()))
                      fun p10 =>
                    Expr.jump Js.fst (Arg.var pw.fst, Arg.var p10.fst, ())) Blocks.nil)
                  fun Jkn =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i64 Ty.bool (by decide))
                  (Arg.var tl_bv, Arg.imm 2, ())) fun p11 =>
                Expr.jnz (Arg.var p11.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_l, ())) fun p12 =>
                   Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                     (Arg.var p12.fst, Arg.var n2, ())) fun p13 =>
                   Expr.jnz (Arg.var p13.fst)
                     (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_l, ())) fun p14 =>
                      Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p15 =>
                      Expr.let_ (Op.mk (OpCode.shl i64)
                        (Arg.var p14.fst, Arg.var p15.fst, ())) fun p16 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p16.fst, Arg.imm 1, ())) fun p17 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p17.fst, Arg.imm 4, ())) fun p18 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var pWvec, Arg.var p18.fst, ())) fun p19 =>
                      Expr.load i32 (Arg.var p19.fst) fun ld_w =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_w, ())) fun p20 =>
                      Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p21 =>
                      Expr.let_ (Op.mk (OpCode.shl i64)
                        (Arg.var p20.fst, Arg.var p21.fst, ())) fun p22 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var pk.fst, Arg.var p22.fst, ())) fun p23 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p23.fst, Arg.imm 4, ())) fun p24 =>
                      Expr.jump Jkn.fst (Arg.var p24.fst, ()))
                     (Expr.jump Jkn.fst (Arg.var pk.fst, ())))
                  (Expr.jump Jkn.fst (Arg.var pk.fst, ()))))
            (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var rpj, Arg.imm 1, ())) fun p25 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p25.fst, Arg.var tl_bv, ())) fun p26 =>
             Expr.jump J_a (Arg.var p26.fst, Arg.var r_cnt', Arg.var pk.fst,
               Arg.var fit_a, Arg.var j, ()))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var w_estj, Arg.imm 0, ())) mk0 := by
  subst hpTmp hpScr hpWvec htl_bv hr_cnt' hfit_a
  have hdw_sr := hinv_r.1
  have hsc32 := bve_scratch_cap_lt32 (c := c)
  refine wp_loop_fwd (fun μk (xs : Tup Val [i64, i32]) mk => ∃ sk,
      xs.2.1.toNat ≤ tl_r ∧ μk = tl_r - xs.2.1.toNat ∧
      BveCopyInv c F0 F_cur sr rpj tl_r xs.2.1 sk mk R) ?_ ?_
  · intro J_k hJ_k; elim_steps_nogrp
    exact hJ_k _ _ _ ⟨_, Nat.zero_le _, rfl,
      bve_copy_init hdw_sr hinv_r.2.1 (by omega) htl_lt32 hmk0⟩
  rintro J_k μk ⟨w_estk, k, ⟨⟩⟩ mk ⟨sk, hk_le, rfl, hinv_k⟩ hJ_k
  dsimp only at hk_le hinv_k
  have hdw_k := hinv_k.1
  have hcv_k := hinv_k.2.2.1
  have hm_k := hinv_k.2.2.2.2.2.2.2.2.2.2.2.2
  elim_steps_nogrp
  · have hk_lt : k.toNat < tl_r := by
      have h := ‹BitVec.toNat k < tl_r % 2 ^ 64›
      rw [Nat.mod_eq_of_lt (by omega)] at h; exact h
    have hk_tmp : k.toNat < sk.core.tmp.length := by
      rw [hdw_k.1.core_ok.tmp_len_arr]
      have := hdw_k.1.core_ok.cur_vars_le; omega
    have hidx_eq : (rpj + 1#64 + BitVec.setWidth 64 k).toNat = rpj.toNat + 1 + k.toNat := by
      have h1 : (rpj + 1#64).toNat = rpj.toNat + 1 := by simp [BitVec.toNat_add]; omega
      simp [BitVec.toNat_add, h1]; omega
    have hcopy_idx : (rpj + 1#64 + BitVec.setWidth 64 k).toNat <
        sk.scratch.scratch_buf.length := by
      rw [hdw_k.1.scratch_ok.scratch_buf_len, hidx_eq]; omega
    elim_steps_nogrp
    refine wp_join_fwd (fun (_ : Tup Val [i64]) mk' => ∃ sk',
        BveCopyInv c F0 F_cur sr rpj tl_r (k + 1#32) sk' mk' R) ?_ ?_
    · intro Jkn hJkn
      have htmp_eq : sk.core.tmp = sr.core.tmp := hinv_k.2.2.2.2.2.2.1
      have hlk_lt : sk.core.tmp[k.toNat].toNat < 2 * sr.core.cur_vars := by
        have h := hbd_r k.toNat hk_lt
        rw [← htmp_eq, List.getElem?_eq_getElem hk_tmp, Option.getD_some] at h
        exact h
      have hswk : (BitVec.setWidth 64 k).toNat = k.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      let sk1 : FullState :=
        { core := sk.core,
          scratch := { sk.scratch with
            scratch_buf := sk.scratch.scratch_buf.set
              (rpj.toNat + 1 + k.toNat) (sk.core.tmp[k.toNat]) } }
      have hms : (FullMem c sk1 ⋆ R) m := by
        simpa [sk1, hidx_eq, hswk] using hm
      have hcp' := bve_copy_step hinv_k hk_lt hbd_rp hk_tmp hms
      have hdw_k1 : FullDenseInvW c F0 F_cur sk1 := hcp'.1
      have hm_k1 : (FullMem c sk1 ⋆ R) _ := hcp'.2.2.2.2.2.2.2.2.2.2.2.2
      have hwv_k : ((BitVec.setWidth 64 sk.core.tmp[(BitVec.setWidth 64 k).toNat] <<<
          BitVec.signExtend 64 1#32) + 1#64).toNat < sk1.core.wvec.length := by
        rw [hdw_k1.1.core_ok.wvec_len]
        have := hdw_k.1.core_ok.cur_vars_le
        have hcv31' := bve_cur_vars_lt31 hdw_sr.1
        have hse1 : (BitVec.signExtend 64 1#32).toNat = 1 := by decide
        have hsh : (BitVec.setWidth 64 sk.core.tmp[k.toNat] <<<
            BitVec.signExtend 64 1#32).toNat = 2 * sk.core.tmp[k.toNat].toNat := by
          change (BitVec.setWidth 64 sk.core.tmp[k.toNat] <<<
            (BitVec.signExtend 64 1#32).toNat).toNat = _
          rw [hse1, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          simp; omega
        simp only [hswk]
        rw [BitVec.toNat_add, hsh]
        simp [Nat.mod_eq_of_lt (by omega : 2 * sk.core.tmp[k.toNat].toNat + 1 < 2 ^ 64)]
        omega
      elim_steps_nogrp
      · exact hJkn _ _ ⟨sk1, hcp'⟩
      · exact hJkn _ _ ⟨sk1, hcp'⟩
      · exact hJkn _ _ ⟨sk1, hcp'⟩
    · rintro _ ⟨w_estk', ⟨⟩⟩ mk' ⟨sk', hcp'⟩; elim_steps_nogrp
      exact hJ_k _ (w_estk', k + 1#32, ()) mk'
        (by simp [BitVec.toNat_add]; omega)
        ⟨sk', hcp'.2.2.2.2.2.2.2.2.2.2.1, rfl, hcp'⟩
  · have htl_len : tl_r ≤ sr.core.tmp.length := by
      rw [hdw_sr.1.core_ok.tmp_len_arr]
      have := hdw_sr.1.core_ok.cur_vars_le; omega
    have hk_nlt : ¬ k.toNat < tl_r := by
      have h := ‹¬ BitVec.toNat k < tl_r % 2 ^ 64›
      rw [Nat.mod_eq_of_lt (by omega)] at h; exact h
    exact hJ_a w_estk _ mk
      (bve_copy_done hinv_r hnp_le hnn_le hinv_k hk_nlt hbd_rp htl_len hbd_r hnd_r hent_r)

theorem wp_bve_var_gates {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s2 : FullState} {m2 : Mem 64} {R : Mem 64 → Prop}
    {m8 m8_b : Bool} {v np nn : BitVec 32} {h r_off : BitVec 64}
    {bodies : Tup Cont [[]] → Blocks Val Cont rs [[]]}
    (hGatesFid : Γ.Has "full_bve_gates_fid" Definition.Spec.m8BveGatesSpec)
    (hGatesM7 : Γ.Has "full_bve_gates_m7" Definition.Spec.fullBveGatesM7Spec)
    (hh : h = c.hdr) (hm8 : m8 = decide (16384 ≤ c.scratch_cap)) (hm8_b : m8_b = m8)
    (h2048 : 2048 ≤ c.scratch_cap) (hv0 : v.toNat < s0.core.cur_vars)
    (h_roff : r_off.toNat = bveROff m8) (hro_le : bveROff m8 ≤ c.scratch_cap)
    (hdw2 : FullDenseInvW c F0 F_cur s2) (htmk2 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars)
    (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hnp_le : np.toNat ≤ bveOccLim m8) (hnn_le : nn.toNat ≤ bveOccLim m8)
    (hent_p2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hent_n2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hk : ∀ (Jg : Cont []) (sg : FullState) (mg : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn r_off 0#64 0#64 true sg.scratch.res_sz sg mg R →
      wp Γ Q X ((bodies (Jg, ())).get Member.here ()) mg) :
    wp Γ Q X (Expr.group bodies fun Jg =>
      Expr.jnz (Arg.var m8_b)
        (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_bve_gates_fid"
          (Arg.var h, Arg.var v, Arg.var np, Arg.var nn, ()) fun _ => Expr.jump Jg.fst ())
        (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_bve_gates_m7"
          (Arg.var h, Arg.var v, Arg.var np, Arg.var nn, ()) fun _ => Expr.jump Jg.fst ()))
      m2 := by
  subst hh hm8_b
  refine wp_join_fwd (fun _ mg => ∃ sg : FullState,
      BveVarLoopsInv c F0 F_cur s0 m8_b v np nn r_off 0#64 0#64 true
        sg.scratch.res_sz sg mg R) ?_ ?_
  · intro Jg hJg; elim_steps_nogrp
    · have hm8t : m8_b = true := ‹_›
      have h16 : 16384 ≤ c.scratch_cap := by
        have h := hm8.symm.trans hm8t; exact of_decide_eq_true h
      refine wp_call_of_spec _ _ (hGatesFid _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk2, h16, (by rw [hcv2]; exact hv0),
        (by simpa [hm8t, bveOccLim] using hnp_le),
        (by simpa [hm8t, bveOccLim] using hnn_le),
        (fun i hi => by simpa using hent_p2 i hi),
        (fun j hj => by simpa [hm8t, bveOccLim] using hent_n2 j hj), hm2, ?_⟩
      rintro sg mg hdwg htmkg hcvg harg halg hflg hscp hscn hmg
      elim_steps_nogrp
      exact hJg () mg ⟨sg, bve_gates_post_inv (s_start := s0) (s0 := s2)
        hcv2 hfl2 hent_p2 (fun j hj => by simpa [hm8t] using hent_n2 j hj) h_roff
        (by rw [h_roff]; exact hro_le) hdwg htmkg hcvg harg halg hflg
        (fun i hi => by simpa using hscp i hi)
        (fun j hj => by simpa [hm8t, bveOccLim] using hscn j hj) hmg⟩
    · have hm8f : m8_b = false := ‹_›
      have h1088 : 1088 ≤ c.scratch_cap := by omega
      refine wp_call_of_spec _ _ (hGatesM7 _ _ _ _ ?_)
      refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk2, h1088, (by rw [hcv2]; exact hv0),
        (by simpa [hm8f, bveOccLim] using hnp_le),
        (by simpa [hm8f, bveOccLim] using hnn_le),
        (fun i hi => by simpa using hent_p2 i hi),
        (fun j hj => by simpa [hm8f, bveOccLim] using hent_n2 j hj), hm2, ?_⟩
      rintro sg mg hdwg htmkg hcvg harg halg hflg hscp hscn hmg
      elim_steps_nogrp
      exact hJg () mg ⟨sg, bve_gates_post_inv (s_start := s0) (s0 := s2)
        hcv2 hfl2 hent_p2 (fun j hj => by simpa [hm8f] using hent_n2 j hj) h_roff
        (by rw [h_roff]; exact hro_le) hdwg htmkg hcvg harg halg hflg
        (fun i hi => by simpa using hscp i hi)
        (fun j hj => by simpa [hm8f, bveOccLim] using hscn j hj) hmg⟩
  · rintro Jg _ mg ⟨sg, hinvg⟩
    exact hk Jg sg mg hinvg

theorem wp_bve_var_resolve {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sj : FullState} {mj : Mem 64} {R : Mem 64 → Prop}
    {m8 : Bool} {v np nn j e_p e_n : BitVec 32}
    {h pTmp pVals pScr pWvec n2 max_r scap_bv rpj r_cntj w_estj res_szj res_sz' : BitVec 64}
    {fit_a : Bool}
    {J_in : Cont [i64, i64, i64, i64, i32]}
    {J17 : Cont [i64, i64, i64, Ty.bool, i64, i32]}
    {J_a : Cont [i64, i64, i64, Ty.bool, i32]}
    (hResolve : Γ.Has "full_bve_resolve_pair" Spec.fullBveResolvePairSpec)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    (hh : h = c.hdr) (hpTmp : pTmp = c.pTmp) (hpVals : pVals = c.pVals)
    (hpScr : pScr = c.pScratchBuf) (hpWvec : pWvec = c.pWvec)
    (hscap : scap_bv = BitVec.ofNat 64 c.scratch_cap)
    (hfit_a : fit_a = true) (hv0 : v.toNat < s0.core.cur_vars)
    (hnp_le : np.toNat ≤ bveOccLim m8) (hnn_le : nn.toNat ≤ bveOccLim m8)
    (hinv_j : BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_szj sj mj R)
    (hep : FullBveEntryOkW F_cur sj (2 * v.toNat) e_p)
    (hen : FullBveEntryOkW F_cur sj (2 * v.toNat + 1) e_n)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJ_in_f : ∀ (sa : FullState) (ma : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj true res_sz' sa ma R →
      J_in (rpj, r_cntj, w_estj, res_sz', j + 1#32, ()) ma)
    (hJ17_f : ∀ (sr : FullState) (mr : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj (r_cntj + 1#64) w_estj false res_sz' sr mr R →
      J17 (rpj, r_cntj + 1#64, w_estj, false, res_sz', j, ()) mr)
    (hJ_a_f : ∀ (rp' r_cnt' w_est' : BitVec 64) (sr : FullState) (mr : Mem 64),
      BveVarLoopsInv c F0 F_cur s0 m8 v np nn rp' r_cnt' w_est' true res_sz' sr mr R →
      J_a (rp', r_cnt', w_est', true, j, ()) mr) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32, i32]) (bs := [Ty.bool]) "full_bve_resolve_pair"
        (Arg.var h, Arg.var v, Arg.var e_p, Arg.var e_n, ()) fun p_ok =>
      Expr.jnz (Arg.var p_ok.fst)
        (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 192, ())) fun p_tl =>
         Expr.load i64 (Arg.var p_tl.fst) fun ld_tl =>
         Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
           (Arg.var ld_tl, Arg.imm 0, ())) fun p_z =>
         Expr.jnz (Arg.var p_z.fst)
           (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1144, ())) fun p_rs =>
            Expr.store (t := i64) (Arg.var res_sz') (Arg.var p_rs.fst)
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun p_in =>
               Expr.store (t := i64) (Arg.imm 1) (Arg.var p_in.fst) (Expr.ret (Arg.imm 20, ()))))
           (Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
             (Arg.var ld_tl, Arg.imm 1, ())) fun p_one =>
            Expr.jnz (Arg.var p_one.fst)
              (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 0, ())) fun p0 =>
               Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pTmp, Arg.var p1.fst, ())) fun p2 =>
               Expr.load i32 (Arg.var p2.fst) fun ld_u =>
               Expr.group (fun (_Js22 : Tup Cont [[]]) =>
                 Blocks.cons (fun _ =>
                   Expr.let_ (Op.mk (OpCode.add i32) (Arg.var j, Arg.imm 1, ())) fun pj1 =>
                   Expr.jump J_in (Arg.var rpj, Arg.var r_cntj, Arg.var w_estj,
                     Arg.var res_sz', Arg.var pj1.fst, ())) Blocks.nil) fun Js22 =>
               Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_u, ())) fun p3 =>
               Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                 (Arg.var p3.fst, Arg.var n2, ())) fun p4 =>
               Expr.jnz (Arg.var p4.fst)
                 (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_u, ())) fun p5 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pVals, Arg.var p5.fst, ())) fun p6 =>
                  Expr.load i8 (Arg.var p6.fst) fun ld_v =>
                  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p7 =>
                  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p8 =>
                  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p7.fst, ())) fun p9 =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.slt i32 Ty.bool (by decide))
                    (Arg.var p8.fst, Arg.var p9.fst, ())) fun p10 =>
                  Expr.jnz (Arg.var p10.fst)
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1144, ())) fun p11 =>
                     Expr.store (t := i64) (Arg.var res_sz') (Arg.var p11.fst)
                       (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun p12 =>
                        Expr.store (t := i64) (Arg.imm 1) (Arg.var p12.fst)
                          (Expr.ret (Arg.imm 20, ()))))
                    (Expr.group (fun (_Js23 : Tup Cont [[]]) =>
                       Blocks.cons (fun _ => Expr.jump Js22.fst ()) Blocks.nil) fun Js23 =>
                     Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p13 =>
                     Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p14 =>
                     Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p13.fst, ())) fun p15 =>
                     Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 Ty.bool (by decide))
                       (Arg.var p14.fst, Arg.var p15.fst, ())) fun p16 =>
                     Expr.jnz (Arg.var p16.fst)
                       (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
                         (Arg.var h, Arg.var ld_u, Arg.imm 4294967295, Arg.imm 0, ()) fun _ =>
                        Expr.jump Js23.fst ())
                       (Expr.jump Js23.fst ())))
                 (Expr.jump Js22.fst ()))
              (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var r_cntj, Arg.imm 1, ())) fun p_rc =>
               Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                 (Arg.var ld_tl, Arg.imm 100, ())) fun p_c1 =>
               Expr.jnz (Arg.var p_c1.fst)
                 (Expr.jump J17 (Arg.var rpj, Arg.var p_rc.fst, Arg.var w_estj,
                   Arg.imm false, Arg.var res_sz', Arg.var j, ()))
                 (Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                   (Arg.var p_rc.fst, Arg.var max_r, ())) fun p_c2 =>
                  Expr.jnz (Arg.var p_c2.fst)
                    (Expr.jump J17 (Arg.var rpj, Arg.var p_rc.fst, Arg.var w_estj,
                      Arg.imm false, Arg.var res_sz', Arg.var j, ()))
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var rpj, Arg.imm 1, ())) fun p_rp1 =>
                     Expr.let_ (Op.mk (OpCode.add i64)
                       (Arg.var p_rp1.fst, Arg.var ld_tl, ())) fun p_rp2 =>
                     Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                       (Arg.var p_rp2.fst, Arg.var scap_bv, ())) fun p_c3 =>
                     Expr.jnz (Arg.var p_c3.fst)
                       (Expr.jump J17 (Arg.var rpj, Arg.var p_rc.fst, Arg.var w_estj,
                         Arg.imm false, Arg.var res_sz', Arg.var j, ()))
                       (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var rpj, Arg.imm 4, ())) fun p_off =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var pScr, Arg.var p_off.fst, ())) fun p_adr =>
                        Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var ld_tl, ())) fun p_tr =>
                        Expr.store (t := i32) (Arg.var p_tr.fst) (Arg.var p_adr.fst)
                          (Expr.group (fun (Js : Tup Cont [[i64, i32]]) =>
                            Blocks.cons (fun pk =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64)
                                (Arg.var pk.snd.fst, ())) fun p0 =>
                              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                                (Arg.var p0.fst, Arg.var ld_tl, ())) fun p1 =>
                              Expr.jnz (Arg.var p1.fst)
                                (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                   (Arg.var pk.snd.fst, ())) fun p2 =>
                                 Expr.let_ (Op.mk (OpCode.mul i64)
                                   (Arg.var p2.fst, Arg.imm 4, ())) fun p3 =>
                                 Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var pTmp, Arg.var p3.fst, ())) fun p4 =>
                                 Expr.load i32 (Arg.var p4.fst) fun ld_l =>
                                 Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var rpj, Arg.imm 1, ())) fun p5 =>
                                 Expr.let_ (Op.mk (OpCode.zext 32 64)
                                   (Arg.var pk.snd.fst, ())) fun p6 =>
                                 Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var p5.fst, Arg.var p6.fst, ())) fun p7 =>
                                 Expr.let_ (Op.mk (OpCode.mul i64)
                                   (Arg.var p7.fst, Arg.imm 4, ())) fun p8 =>
                                 Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var pScr, Arg.var p8.fst, ())) fun p9 =>
                                 Expr.store (t := i32) (Arg.var ld_l) (Arg.var p9.fst)
                                   (Expr.group (fun (_Jkn : Tup Cont [[i64]]) =>
                                      Blocks.cons (fun pw =>
                                        Expr.let_ (Op.mk (OpCode.add i32)
                                          (Arg.var pk.snd.fst, Arg.imm 1, ())) fun p10 =>
                                        Expr.jump Js.fst (Arg.var pw.fst, Arg.var p10.fst, ()))
                                        Blocks.nil) fun Jkn =>
                                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i64 Ty.bool (by decide))
                                      (Arg.var ld_tl, Arg.imm 2, ())) fun p11 =>
                                    Expr.jnz (Arg.var p11.fst)
                                      (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                         (Arg.var ld_l, ())) fun p12 =>
                                       Expr.let_ (Op.mk
                                         (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                                         (Arg.var p12.fst, Arg.var n2, ())) fun p13 =>
                                       Expr.jnz (Arg.var p13.fst)
                                         (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                            (Arg.var ld_l, ())) fun p14 =>
                                          Expr.let_ (Op.mk (OpCode.sext 32 64)
                                            (Arg.imm 1, ())) fun p15 =>
                                          Expr.let_ (Op.mk (OpCode.shl i64)
                                            (Arg.var p14.fst, Arg.var p15.fst, ())) fun p16 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var p16.fst, Arg.imm 1, ())) fun p17 =>
                                          Expr.let_ (Op.mk (OpCode.mul i64)
                                            (Arg.var p17.fst, Arg.imm 4, ())) fun p18 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var pWvec, Arg.var p18.fst, ())) fun p19 =>
                                          Expr.load i32 (Arg.var p19.fst) fun ld_w =>
                                          Expr.let_ (Op.mk (OpCode.zext 32 64)
                                            (Arg.var ld_w, ())) fun p20 =>
                                          Expr.let_ (Op.mk (OpCode.sext 32 64)
                                            (Arg.imm 1, ())) fun p21 =>
                                          Expr.let_ (Op.mk (OpCode.shl i64)
                                            (Arg.var p20.fst, Arg.var p21.fst, ())) fun p22 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var pk.fst, Arg.var p22.fst, ())) fun p23 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var p23.fst, Arg.imm 4, ())) fun p24 =>
                                          Expr.jump Jkn.fst (Arg.var p24.fst, ()))
                                         (Expr.jump Jkn.fst (Arg.var pk.fst, ())))
                                      (Expr.jump Jkn.fst (Arg.var pk.fst, ()))))
                                (Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var rpj, Arg.imm 1, ())) fun p25 =>
                                 Expr.let_ (Op.mk (OpCode.add i64)
                                   (Arg.var p25.fst, Arg.var ld_tl, ())) fun p26 =>
                                 Expr.jump J_a (Arg.var p26.fst, Arg.var p_rc.fst, Arg.var pk.fst,
                                   Arg.var fit_a, Arg.var j, ()))) Blocks.nil)
                            fun Js => Expr.jump Js.fst (Arg.var w_estj, Arg.imm 0, ()))))))))
        (Expr.jump J_a (Arg.var rpj, Arg.var r_cntj, Arg.var w_estj,
          Arg.var fit_a, Arg.var j, ()))) mj := by
  subst hh hpTmp hpVals hpScr hpWvec hscap hfit_a
  have hdw_j := hinv_j.1; have hm_j := hinv_j.2.2.2.2.2.2.2.2.2
  have hsc32 := bve_scratch_cap_lt32 (c := c)
  refine wp_call_of_spec _ _ (hResolve _ _ _ _ ?_)
  refine ⟨c, F0, F_cur, sj, R, rfl, hdw_j,
    (by dsimp only [Arg.val]; have := hinv_j.2.2.1; omega), hep, hen, hm_j, ?_⟩
  intro ok_r lm_r tmp_r tl_r mr sr_spec hdw_r htl_le_r hok_r hm_r
  dsimp only
  let sr : FullState :=
    { core := { sj.core with lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r }
      scratch := sj.scratch }
  have hdw_sr : FullDenseInvW c F0 F_cur sr := hdw_r
  have hcv_r : sr.core.cur_vars = sj.core.cur_vars := rfl
  have hfl_r : sr.core.fuel.toNat ≤ sj.core.fuel.toNat := Nat.le_refl _
  have har_r : sr.core.arena = sj.core.arena := rfl
  have hal_r : sr.core.arena_len = sj.core.arena_len := rfl
  have hscr_r : sr.scratch = sj.scratch := rfl
  have htl_lt32 : tl_r < 2 ^ 32 := by
    have := hdw_j.1.core_ok.cur_vars_le; have := bve_cur_vars_lt31 hdw_j.1; omega
  elim_steps_nogrp
  · obtain ⟨_, _, hent_r⟩ := hok_r ‹ok_r = true›
    have htl0 : tl_r = 0 := by
      have h : BitVec.ofNat 64 tl_r = 0#64 := ‹_›
      have h' := congrArg BitVec.toNat h
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64)] at h'; exact h'
    have hres_r0 := bve_rlen0_ret20 res_sz' hdw_sr
      (by simpa [TmkZero] using hinv_j.2.1) (hcv_r.trans hinv_j.2.2.1)
      (Nat.le_trans hfl_r hinv_j.2.2.2.1) (by simpa [sr, htl0] using hent_r)
    exact bve_ret_q hQ ⟨hres_r0.1, hres_r0.2.1, hres_r0.2.2.1,
      hres_r0.2.2.2.1, Or.inr (Or.inr rfl), fun _ => hres_r0.2.2.2.2⟩ ‹_›
  · obtain ⟨hbd_r, _, hent_r⟩ := hok_r ‹ok_r = true›
    have htl1 : tl_r = 1 := by
      have h : BitVec.ofNat 64 tl_r = 1#64 := ‹_›
      have h' := congrArg BitVec.toNat h
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64)] at h'; exact h'
    refine wp_bve_var_rlen1 hAssign rfl rfl rfl hinv_j hdw_sr hcv_r hfl_r har_r hal_r
      hscr_r hm_r (by simpa [sr, htl1] using hbd_r) (by simpa [sr, htl1] using hent_r) hQ ?_
    intro _ sa ma hinv_a
    elim_steps_nogrp
    exact hJ_in_f sa ma hinv_a
  · exact hJ17_f sr mr (bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r)
  · exact hJ17_f sr mr (bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r)
  · exact hJ17_f sr mr (bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r)
  · obtain ⟨hbd_r, hnd_r, hent_r⟩ := hok_r ‹ok_r = true›
    have hinv_r : BveVarLoopsInv c F0 F_cur s0 m8 v np nn rpj r_cntj w_estj
        true res_sz' sr mr R :=
      bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r
    have hbd_rp : rpj.toNat + 1 + tl_r ≤ c.scratch_cap := by
      have hrp_le := hinv_j.2.2.2.2.2.2.2.1
      have hnrp : ¬ c.scratch_cap % 2 ^ 64 <
          (rpj.toNat + BitVec.toNat (1#64) + sr_spec.core.tmp_len) % 2 ^ 64 := ‹_›
      change ¬ c.scratch_cap % 2 ^ 64 < (rpj.toNat + 1 + tl_r) % 2 ^ 64 at hnrp
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnrp; omega
    have hrp_lt : rpj.toNat < sr.scratch.scratch_buf.length := by
      rw [hdw_sr.1.scratch_ok.scratch_buf_len]; omega
    elim_steps_nogrp
    have htr : BitVec.truncate 32 (BitVec.ofNat 64 tl_r) = BitVec.ofNat 32 tl_r := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.truncate, BitVec.toNat_ofNat]
    exact wp_bve_var_copy_loop (sr := sr) rfl rfl rfl rfl htl_lt32 htl_le_r rfl rfl
      hnp_le hnn_le hinv_r hbd_rp (by simpa [sr] using hbd_r) (by simpa [sr] using hnd_r)
      (by simpa [sr] using hent_r) (by simpa [sr, sr_spec, htr] using hm)
      (fun w_estk s_done mk hinv_d => hJ_a_f _ _ _ s_done mk hinv_d)
  · exact hJ_a_f _ _ _ sr mr
      (bve_loops_resolve_post hinv_j hdw_sr hcv_r hfl_r har_r hal_r hscr_r hm_r)

end

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
