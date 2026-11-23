/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1b
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1c

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 1 (`full_propagate_ignore_hot_wp`)

Zero `import all`, plain `public section` (`0` `@[expose]`).
Proves `full_propagate_ignore_hot_wp` directly against `FullPropDecSpecs.fullPropagateIgnoreSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "m7_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "m7_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "m7_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

private def M7OuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (rem : Nat)
    (prop_v tend_v unass_v unfl_v _ticks_v : BitVec 64) (m : Mem 64) : Prop :=
  ∃ (sem : FullState) (te_mem : Nat),
    rem = sem.core.fuel.toNat ∧
    sem.LengthsOk c ∧
    FullWitnessInv c F0 F_cur sem.core ∧
    FullPropDecSpecs.FullTrailExt s.core sem.core ∧
    FullPropDecSpecs.FullArenaPermEq s.core sem.core ∧
    AgreesExcept m7CoreMask s.core sem.core ∧
    sem.core.propagated = prop_v.toNat ∧
    sem.core.trail_end = tend_v.toNat ∧
    sem.core.unassigned = unass_v ∧
    sem.core.unflushed = unfl_v ∧
    sem.core.oom = 0#64 ∧
    sem.core.confl_type = s.core.confl_type ∧
    sem.core.dense_mode = 0#64 ∧
    sem.core.cur_vars = s.core.cur_vars ∧
    sem.core.cur_level = s.core.cur_level ∧
    sem.core.probing = s.core.probing ∧
    sem.core.arena_len = s.core.arena_len ∧
    sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
    s.core.propagated ≤ prop_v.toNat ∧
    te_mem ≤ sem.core.trail_end ∧
    s.core.propagated ≤ te_mem ∧
    sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases } ∧
    (FullMem c
      (fastPropMem
        { s with
          core := { s.core with trail_end := te_mem } }
        { sem with
          core := { sem.core with propagated := s.core.propagated } }) ⋆ R) m

private theorem m7_outer_flush_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {ignore_ref prop_v tend_v unass_v unfl_v ticks' r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
              wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch :=
            { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullConflOkW F_cur s'.core ∧ (ctype' = 2#64 → cref' ≠ ignore_ref) ∧
        (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7CoreMask s.core sem.core)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hprop_eq : sem.core.propagated = prop_v.toNat)
    (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hunass_eq : sem.core.unassigned = unass_v)
    (hunfl_eq : sem.core.unflushed = unfl_v)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hr0 : r = 0#64 → prop_v.toNat = tend_v.toNat ∧ sem.core.confl_type = s.core.confl_type ∧
      (s.core.oom = 0#64 → sem.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → sem.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : r ≠ 1#64)
    (hr2 : r = 2#64 → sem.core.oom ≠ 0#64 ∨ sem.core.fuel = 0#64)
    (hm : (FullMem c
      { sem with
        core :=
          { sem.core with
            propagated := prop_v.toNat, trail_end := tend_v.toNat
            unassigned := unass_v, unflushed := unfl_v }
        scratch := { sem.scratch with search_ticks := ticks' } } ⋆ R) m) :
    Q (r, ()) m := by
  let sem_fin : FullState :=
    { sem with
      core :=
        { sem.core with
          propagated := prop_v.toNat, trail_end := tend_v.toNat
          unassigned := unass_v, unflushed := unfl_v }
      scratch := { sem.scratch with search_ticks := ticks' } }
  have hfin_core :
      { sem.core with
        propagated := prop_v.toNat, trail_end := tend_v.toNat
        unassigned := unass_v, unflushed := unfl_v } = sem.core := by
    rw [← hprop_eq, ← htend_eq, ← hunass_eq, ← hunfl_eq]
  have hlen_fin : sem_fin.LengthsOk c :=
    ⟨by simp only [sem_fin, hfin_core]; exact hlen_o.core_ok,
     by dsimp only [sem_fin]; exact { hlen_o.scratch_ok with }⟩
  have hw_fin : FullWitnessInv c F0 F_cur sem_fin.core := by
    simp only [sem_fin, hfin_core]; exact hw_o
  have htr_fin : FullPropDecSpecs.FullTrailExt s.core sem_fin.core := by
    simp only [sem_fin, hfin_core]; exact htr_o
  have hperm_fin : FullPropDecSpecs.FullArenaPermEq s.core sem_fin.core := by
    simp only [sem_fin, hfin_core]; exact hperm_o
  have hag_fin : AgreesExcept m7CoreMask s.core sem_fin.core := by
    simp only [sem_fin, hfin_core]; exact hag_o
  have hsc_fin : sem_fin.scratch = { s.scratch with
      search_ticks := sem_fin.scratch.search_ticks, wsort := sem_fin.scratch.wsort,
      phases := sem_fin.scratch.phases } := by
    dsimp only [sem_fin]; rw [hsc_o]
  exact m7_exit_hQ c F0 F_cur s ignore_ref R Q hQ r sem_fin m
    hag_fin hsc_fin hlen_fin hw_fin htr_fin hperm_fin
    (by simp only [sem_fin]; exact hfuel_le) hr
    (fun h => by dsimp only [sem_fin]; exact hr0 h)
    (fun h => absurd h hr1)
    (fun h => by dsimp only [sem_fin]; exact hr2 h)
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private def m7PostLpOvfExpr (c : FullCfg) (not_lit_v : Val i32) (off_o end_o : Val i64)
    (Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (te_p un_p uf_p tk_p p_p q_p brk_p : Val i64) (ovf_p : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64]])
    (fun _Js0 => Blocks.cons
      (fun p1 => Expr.jump Lo
        (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p, Arg.var p1.fst,
          Arg.var p1.snd.fst, Arg.var p1.snd.snd.fst, Arg.var p1.snd.snd.snd.fst,
          Arg.var p1.snd.snd.snd.snd.fst, Arg.var ovf_p, ()))
      Blocks.nil)
    (fun Js0 =>
      Expr.jnz (Arg.var ovf_p)
        (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool]) "full_prop_lit_ovf_hot"
          (Arg.var c.hdr, Arg.var ovf_rw_p, Arg.var ovf_oth_p, Arg.var ovf_cr_p, ()) fun pok =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var c.hdr, Arg.imm 104, ())⟩ fun wvp =>
        Expr.load i64 (Arg.var wvp.fst) fun wv =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var not_lit_v, ())⟩ fun nl64 =>
        Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.shl i64, (Arg.var nl64.fst, Arg.var s1.fst, ())⟩ fun idx =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var idx.fst, Arg.imm 4, ())⟩ fun boff =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wv, Arg.var boff.fst, ())⟩ fun addr =>
        Expr.load i32 (Arg.var addr.fst) fun noff32 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noff32, ())⟩ fun noff =>
        Expr.group (sig := [[i64, i64, i64, i64]])
          (fun _Jn => Blocks.cons
            (fun pn =>
              Expr.jnz (Arg.var pok.fst)
                (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovf_cr_p, ())⟩ fun cr64 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var cr64.fst, Arg.imm 3, ())⟩ fun obase =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var obase.fst, Arg.imm 4, ())⟩ fun b3 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b3.fst, ())⟩ fun a3 =>
                Expr.store (Arg.var ovf_oth_p) (Arg.var a3.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.imm 1, ())⟩ fun ob1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var ob1.fst, Arg.imm 4, ())⟩ fun b4 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b4.fst, ())⟩ fun a4 =>
                Expr.store (Arg.var ovf_rw_p) (Arg.var a4.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.var ovf_ri_p, ())⟩ fun obri =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var obri.fst, Arg.imm 4, ())⟩ fun bri =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var bri.fst, ())⟩ fun ari =>
                Expr.store (Arg.var not_lit_v) (Arg.var ari.fst) $
                Expr.jump Js0.fst
                  (Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var pn.snd.snd.fst,
                    Arg.var pn.snd.snd.snd.fst, Arg.var brk_p, ()))
                (Expr.let_ ⟨OpCode.mul i64, (Arg.var pn.snd.snd.fst, Arg.imm 4, ())⟩ fun bq =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq.fst, ())⟩ fun aq =>
                Expr.store (Arg.var ovf_oth_p) (Arg.var aq.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 1, ())⟩ fun q1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun bq1 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq1.fst, ())⟩ fun aq1 =>
                Expr.store (Arg.var ovf_cr_p) (Arg.var aq1.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 2, ())⟩ fun q2 =>
                Expr.jump Bo
                  (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p,
                    Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var q2.fst,
                    Arg.var pn.snd.snd.snd.fst, Arg.imm 2, Arg.var ovf_p, ())))
            Blocks.nil)
          (fun Jn =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ne i64, (Arg.var noff.fst, Arg.var off_o, ())⟩ fun ne =>
            Expr.jnz (Arg.var ne.fst)
              (Expr.let_ ⟨OpCode.sub i64, (Arg.var q_p, Arg.var off_o, ())⟩ fun qoff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var qoff.fst, ())⟩ fun qn =>
              Expr.let_ ⟨OpCode.sub i64, (Arg.var p_p, Arg.var off_o, ())⟩ fun poff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var poff.fst, ())⟩ fun pn =>
              Expr.let_ ⟨OpCode.sub i64, (Arg.var end_o, Arg.var off_o, ())⟩ fun eoff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var eoff.fst, ())⟩ fun en =>
              Expr.jump Jn.fst
                (Arg.var noff.fst, Arg.var pn.fst, Arg.var qn.fst, Arg.var en.fst, ()))
              (Expr.jump Jn.fst
                (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, ()))))
        (Expr.jump Js0.fst
          (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, Arg.var brk_p, ())))

private theorem m7_post_lp_ovf_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_base s_disk sem_o sem_p : FullState}
    {ignore_ref t0_v off_o p_o end_o te_p un_p uf_p tk_p p_p q_p brk_p : BitVec 64}
    {ovf_p : Bool} {not_lit not_lit_v ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32}
    {ovf_ri_p : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mbp : Mem 64}
    {Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    (hOvf : ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hBo : ∀ xs m,
      (match xs with
        | (te_b, un_b, uf_b, _tk_b, off_b, p_b, q_b, end_b, brk_b, _ovf_b, ()) =>
          ∃ sem_b : FullState,
            PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
              p_b.toNat end_b.toNat ∧
            te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
            uf_b = sem_b.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
            (brk_b = 0#64 →
              sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
              p_b = end_b) ∧
            (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
              sem_b.core.oom = 0#64) ∧
            (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
            (FullMem c (fastPropMem s_disk sem_b) ⋆ R) m) → Bo xs m)
    (ih_o : ∀ rem' xs m,
      rem' < (end_o.toNat - p_o.toNat) + 1 →
      (match xs with
        | (te_o', un_o', uf_o', _tk_o', off_o', p_o', q_o', end_o', brk_o', ovf_o', ()) =>
          ∃ sem_o' : FullState,
            rem' = (end_o'.toNat - p_o'.toNat) + (if ovf_o' then 1 else 0) ∧
            PropLitInv c F0 F_cur s_base sem_o' not_lit.toNat off_o'.toNat q_o'.toNat
              p_o'.toNat end_o'.toNat ∧
            te_o'.toNat = sem_o'.core.trail_end ∧ un_o' = sem_o'.core.unassigned ∧
            uf_o' = sem_o'.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o'.core.trail_end) ∧
            (ovf_o' = true → brk_o' = 0#64 ∧ sem_o'.core.oom = 0#64 ∧
              sem_o'.core.confl_type = s.core.confl_type) ∧
            (ovf_o' = false →
              (brk_o' = 0#64 →
                sem_o'.core.oom = 0#64 ∧ sem_o'.core.confl_type = s.core.confl_type ∧
                p_o' = end_o') ∧
              (brk_o' = 1#64 → PropLitConfl F_cur ignore_ref sem_o'.core ∧
                sem_o'.core.oom = 0#64) ∧
              (brk_o' = 0#64 ∨ brk_o' = 1#64)) ∧
            (FullMem c (fastPropMem s_disk sem_o') ⋆ R) m) → Lo xs m)
    (har : c.arena_cap < 2 * 2 ^ 28) (hwc : c.wcap < 2 * 2 ^ 28)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem_p.core.cur_vars)
    (hsd_pr : s_disk.core.propagated = sem_p.core.propagated)
    (hnot_lt : not_lit.toNat < 2 * sem_p.core.cur_vars)
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hct_o2 : sem_o.core.confl_type = s.core.confl_type)
    (ht0_p : t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end)
    (hnl_eq : not_lit_v = not_lit)
    (hpi_p : PropLitInv c F0 F_cur s_base sem_p not_lit.toNat off_o.toNat
      q_p.toNat p_p.toNat end_o.toNat)
    (_hpo_le_pp : p_o.toNat ≤ p_p.toNat)
    (hte_p : te_p.toNat = sem_p.core.trail_end) (hun_p : un_p = sem_p.core.unassigned)
    (huf_p : uf_p = sem_p.core.unflushed) (hoom_p : sem_p.core.oom = 0#64)
    (hnoov : ovf_p = false →
      (brk_p = 0#64 → p_p = end_o ∧ sem_p.core.confl_type = sem_o.core.confl_type) ∧
      (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
      (brk_p = 0#64 ∨ brk_p = 1#64))
    (hov_yes : ovf_p = true →
      brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
      2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
      end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
      ovf_cr_p.toNat < 0x80000000 ∧
      ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
      ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
        sem_p.core.arena_len ∧
      ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat ≠ not_lit.toNat ∧
      2 ≤ ovf_ri_p.toNat ∧
      ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
      sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hmbp : (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) :
    wp Γ Q X (m7PostLpOvfExpr c not_lit_v off_o end_o Bo Lo
      te_p un_p uf_p tk_p p_p q_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p) mbp := by
  have hmaxv := c.hmaxv
  unfold dimacsBound at hmaxv
  rw [hnl_eq]
  unfold m7PostLpOvfExpr
  m7_hsteps
  m7_hsplit
  · -- `ovf_p == true`: call `full_prop_lit_ovf_hot`
    have hovf_true : ovf_p = true := hc
    have hov_y := hov_yes hovf_true
    subst hovf_true
    obtain ⟨rfl, hct_p, hp_off2, hq_pp2, hrem_dec, hcr_lt, hcr_ref, hcr_fit,
      hoth_lt, hovf_lt, hovf_ne, hri2, hri_lt, har3, har4, har_ri⟩ := hov_y
    have hlen_mp : (fastPropMem s_disk sem_p).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len hpi_p.len hsd_cv.symm hsd_pr.symm rfl
    have hlay_mp : WatchStackLayout (fastPropMem s_disk sem_p).core :=
      fastPropMem_watchLayout hpi_p.sw.layout rfl
    c0_call hOvf
    refine ⟨c, fastPropMem s_disk sem_p, R, rfl, hlen_mp, hlay_mp,
      fun h => absurd h (by decide),
      fun _ => ⟨by
          intro h; rw [h] at hoth_lt
          have h42 : (4294967295#32 : BitVec 32).toNat = 4294967295 := rfl
          rw [h42] at hoth_lt
          have := hpi_p.len.core_ok.cur_vars_le; omega,
        by intro h; rw [h] at hcr_lt; revert hcr_lt; decide⟩,
      hmbp,
      fun pok wv' ws' wl' wu' wsrt' mo' hlen' hlay' hoth_pr hnew_pr hfail_pr hmo' => ?_⟩
    let st4 : FullState :=
      { sem_p with
        core := { sem_p.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { sem_p.scratch with wsort := wsrt' } }
    have hlen4 : st4.LengthsOk c := by
      simp only [fastPropMem_def] at hlen'
      have hso := hlen'.scratch_ok
      have hscr4 : st4.scratch.LengthsOk c :=
        ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8,
         hso.9, hso.10, hso.11, hso.12, hso.13, hso.14, hso.15, hso.16,
         hso.17, hso.18, hso.19, hso.20, hso.21, hso.22, hso.23, hso.24⟩
      exact ⟨{ hlen'.core_ok with
          trail_end_le := hpi_p.len.core_ok.trail_end_le
          propagated_le := hpi_p.len.core_ok.propagated_le }, hscr4⟩
    have hcv4 : st4.core.cur_vars = sem_p.core.cur_vars := rfl
    have hlay4 : WatchStackLayout st4.core := by
      simp only [fastPropMem_def] at hlay'
      exact { bounds := hlay'.bounds, pos_off := hlay'.pos_off,
              disjoint := hlay'.disjoint, no_sentinel := hlay'.no_sentinel }
    have hperm24 : FullPropDecSpecs.FullArenaPermEq sem_p.core st4.core :=
      ⟨rfl, fun r _ => ⟨rfl, rfl, .refl _⟩⟩
    have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
      fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hpi_p.nw rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hag4 : AgreesExcept propLitCoreMask s_base.core st4.core :=
      hpi_p.ag.update (fun k =>
        { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    have htr4 : FullPropDecSpecs.FullTrailExt s_base.core st4.core :=
      ⟨hpi_p.tr.te_ge, hpi_p.tr.trl_pref, hpi_p.tr.lvl_pres⟩
    have hsc4 : st4.scratch = { s_base.scratch with
        search_ticks := st4.scratch.search_ticks,
        wsort := st4.scratch.wsort, phases := st4.scratch.phases } := by
      dsimp only [st4]; rw [hpi_p.sc_eq]
    have hoth_mask : (ovf_oth_p &&& 0x7FFFFFFF#32) = ovf_oth_p :=
      m7_bv32_mask7f_eq (by
        have := hpi_p.cur_vars_eq; have := hpi_p.len.core_ok.cur_vars_le; omega)
    have hp_ge2 : 2 ≤ p_p.toNat := by omega
    have hp_sub2 : (p_p - 2#64).toNat = p_p.toNat - 2 := m7_bv64_sub_toNat hp_ge2
    have hq_le_prev : q_p.toNat ≤ (p_p - 2#64).toNat := by rw [hp_sub2]; omega
    have hp2_back :
        (p_p - 2#64 + 1#64 + 1#64).toNat = (p_p - 2#64).toNat + 2 := by
      have := hpi_p.len.core_ok.wlen_le
      have := hpi_p.end_lt_wcap hnot_lt
      have := hpi_p.sw.p_le_end
      rw [BitVec.toNat_add, BitVec.toNat_add, hp_sub2]
      have h1 : p_p.toNat - 2 + 1 < 2 ^ 64 := by omega
      rw [show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by omega)]
    have hq_le_p' : q_p.toNat ≤ p_p.toNat := hpi_p.sw.q_le_p
    have hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := hpi_p.not_f
    have hmem4 : (FullMem c (fastPropMem s_disk st4) ⋆ R) mo' := by
      simpa only [st4, fastPropMem_def] using hmo'
    have hwvc4 := hlen4.core_ok.wvec_len
    have hoff4_lt_wv : 2 * not_lit.toNat < st4.core.wvec.length := by
      rw [hwvc4]; have := hlen4.core_ok.cur_vars_le; omega
    have hoff4_lt_m : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
        (fastPropMem s_disk st4).core.wvec.length := by
      rw [fastPropMem_wvec, hnl64_idx]; exact hoff4_lt_wv
    have h2n_lt64 : 2 * not_lit.toNat < 2 ^ 64 := by
      have := hlen4.core_ok.cur_vars_le; omega
    have hoff4_mod : 2 * not_lit.toNat % 2 ^ 64 = 2 * not_lit.toNat :=
      Nat.mod_eq_of_lt h2n_lt64
    have hmem_wvec_get : ∀ {i : Nat} (hi : i = 2 * not_lit.toNat)
        (pf : i < (fastPropMem s_disk st4).core.wvec.length),
        ((fastPropMem s_disk st4).core.wvec[i]'pf).setWidth 64 =
        (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 := by
      intro i hi pf
      have hg : (fastPropMem s_disk st4).core.wvec[i]? =
          st4.core.wvec[2 * not_lit.toNat]? := by rw [fastPropMem_wvec, hi]
      rw [List.getElem?_eq_getElem pf, List.getElem?_eq_getElem hoff4_lt_wv,
        Option.some.injEq] at hg
      exact congrArg (BitVec.setWidth 64) hg
    m7_hsteps_nogrp
    refine wp_join_group (fun ((off_n, p_n, q_n, end_n, ()) :
        Tup Val [i64, i64, i64, i64]) mj =>
        mj = mo' ∧
        off_n = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 ∧
        q_n = off_n + (q_p - off_o) ∧
        p_n = off_n + (p_p - off_o) ∧
        end_n = off_n + (end_o - off_o)) ?_ ?_
    · rintro _ ⟨off_n, p_n, q_n, end_n, ⟨⟩⟩ mj ⟨rfl, hoff_n_def, hqn_d, hpn_d, hen_d⟩
      have hpi_p_sh : PropLitInv c F0 F_cur s_base sem_p not_lit.toNat
          off_o.toNat q_p.toNat ((p_p - 2#64).toNat + 2) end_o.toNat := by
        simpa only [show (p_p - 2#64).toNat + 2 = p_p.toNat from by rw [hp_sub2]; omega]
          using hpi_p
      have hpn_d' : p_n = off_n + ((p_p - 2#64) + 1#64 + 1#64 - off_o) := by
        rw [hpn_d, show (p_p - 2#64) + 1#64 + 1#64 = p_p from by
          apply BitVec.eq_of_toNat_eq; rw [hp2_back, hp_sub2]; omega]
      have hoff_n_eq : off_n = BitVec.setWidth 64
          (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
        rw [hoff_n_def, List.getElem?_eq_getElem hoff4_lt_wv, Option.getD_some]
      clear hoff_n_def hpn_d
      subst hqn_d hen_d hpn_d' hoff_n_eq
      m7_hsplit
      · -- `pushed`: swap `[ovf_other, ovf_rw, not_lit]`, continue `while (ovf)`
        have hpok_t : pok = true := hc
        have hok := m7_ovf_ok_step hpi_p_sh hlen4 hcv4 hnot_lt hlay4 hperm24 hnw4
          hag4 htr4 hsc4 hnot_f4 rfl hcr_fit rfl har3 har4 hri2 hri_lt har_ri
          hovf_lt hovf_ne hcr_lt hcr_ref hp2_back hq_le_prev hoth_mask
          (fun l hl hne => by
            have h := hoth_pr l (by simpa only [fastPropMem_def] using hl) hne
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
          (by
            have h := (hnew_pr hpok_t).2.2
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore,
              hoth_mask] using ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 rfl⟩)
        have hcr_u64 : ovf_cr_p.toNat + 3 +
            fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat < 2 ^ 64 := by
          have := hpi_p.len.core_ok.arena_len_le
          exact Nat.lt_of_le_of_lt (Nat.le_trans hcr_fit this) (Nat.lt_trans har (by decide))
        have har_m4 : (fastPropMem s_disk st4).core.arena.length = sem_p.core.arena.length :=
          congrArg List.length (fastPropMem_arena s_disk st4)
        have h3_idx : (BitVec.setWidth 64 ovf_cr_p + 3).toNat = ovf_cr_p.toNat + 3 := by
          rw [BitVec.toNat_add, bv_c0_zext32_64, show (3 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have h31_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat = ovf_cr_p.toNat + 4 := by
          rw [BitVec.toNat_add, h3_idx, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hri_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat =
            ovf_cr_p.toNat + 3 + ovf_ri_p.toNat := by
          rw [BitVec.toNat_add, h3_idx, Nat.mod_eq_of_lt (by omega)]
        have har3_m : (BitVec.setWidth 64 ovf_cr_p + 3).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [h3_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har3).1
        have har31_m : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [h31_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har4).1
        have har_ri_m : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [hri_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har_ri).1
        m7_hsteps
        exact ih_o _ (te_p, un_p, uf_p, tk_p, _, _, _, _, 0#64, true, ()) _
          (by
            simp only [↓reduceIte]
            rw [hok.2.2.2.2.1, show (p_p - 2#64).toNat + 2 = p_p.toNat from by
              rw [hp_sub2]; exact Nat.sub_add_cancel hp_ge2]
            exact Nat.add_lt_add_right hrem_dec 1)
          ⟨_, rfl, hok.2.2.2.2.2, hte_p, hun_p, huf_p, ht0_p,
            fun _ => ⟨rfl, hoom_p, hct_p.trans hct_o2⟩,
            fun h => absurd h (by decide),
            by
              simpa only [fastPropMem_arena, fastPropMem_with_arena,
                h3_idx, h31_idx, hri_idx] using hm⟩
      · -- `!pushed` (`L409-415`): keep large `[ovf_other, ovf_cref]`
        have hpok_f : pok = false := hc
        have hfail := m7_ovf_fail_step hpi_p_sh hlen4 hcv4 hnot_lt
          hlay4 hperm24 hnw4 hag4 htr4 hsc4 hnot_f4 hovf_lt hovf_ne hcr_lt
          hcr_ref hp2_back hq_le_prev hoth_mask
          (fun l hl hne => by
            have h := hoth_pr l (by simpa only [fastPropMem_def] using hl) hne
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
          (by
            have h := (hfail_pr hpok_f).1
              (by simpa only [fastPropMem_def, hpi_p.cur_vars_eq] using hovf_lt)
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
        have hq_wlen :
            (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
              (q_p - off_o)).toNat < (fastPropMem s_disk st4).core.wstk.length := by
          rw [fastPropMem_wstk]; exact hfail.1
        have hq1_wlen :
            (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
              (q_p - off_o) + 1).toNat < (fastPropMem s_disk st4).core.wstk.length := by
          rw [fastPropMem_wstk, show (1 : BitVec 64) = 1#64 from rfl, hfail.2.2.1]
          exact hfail.2.1
        ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps!)
        refine hBo _ _ ⟨_, hfail.2.2.2.2.2.2.2, hte_p, hun_p, huf_p, ht0_p,
          fun h => absurd h (by decide), fun h => absurd h (by decide), Or.inr (Or.inr rfl),
          by
            simpa only [fastPropMem_wstk, fastPropMem_with_wstk,
              show (1 : BitVec 64) = 1#64 from rfl, hfail.2.2.1] using hm⟩
    · -- Join `if (noff != off)` entry (`noff != off` vs `noff == off`)
      intro Jn hJn
      m7_hsplit
      · m7_hsteps
        have hnoff := hmem_wvec_get hnl64_idx hoff4_lt_m
        exact hJn _ mo' ⟨rfl, hnoff, rfl, rfl, rfl⟩
      · m7_hsteps
        have hnoff_eq := hmem_wvec_get hoff4_mod
          (by rw [hoff4_mod, fastPropMem_wvec]; exact hoff4_lt_wv)
        have hoff_eq : off_o = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 :=
          hc.symm.trans hnoff_eq
        have had_sub : ∀ {x : BitVec 64}, off_o.toNat ≤ x.toNat →
            x.toNat < 2 ^ 64 → x = off_o + (x - off_o) := by
          intro x hle hlt
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, m7_bv64_sub_toNat hle, Nat.mod_eq_of_lt (by omega)]
          omega
        have hend_lt : end_o.toNat < 2 ^ 64 :=
          Nat.lt_of_le_of_lt
            (Nat.le_trans (hpi_p.end_lt_wcap hnot_lt).1 (hpi_p.end_lt_wcap hnot_lt).2)
            (Nat.lt_trans hwc (by decide))
        have hq_ge := hpi_p.sw.q_ge
        have hq_le := hpi_p.sw.q_le_p
        have hp_le := hpi_p.sw.p_le_end
        exact hJn _ mo' ⟨rfl, hoff_eq,
          had_sub hq_ge (by omega),
          had_sub (Nat.le_trans hq_ge hq_le) (by omega),
          had_sub (Nat.le_trans hq_ge (Nat.le_trans hq_le hp_le)) hend_lt⟩
  · -- `!(ovf_p)`: exit `while (ovf)` via `Lo` (`ovf_p = false`)
    have hovf_false : ovf_p = false := hc
    subst hovf_false
    have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
    m7_hsteps
    exact ih_o _ (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, brk_p, false, ()) mbp
      (by simp only [Bool.false_eq_true, ↓reduceIte]; have := _hpo_le_pp; omega)
      ⟨sem_p, rfl, hpi_p, hte_p, hun_p, huf_p, ht0_p,
        fun h => absurd h (by decide),
        fun _ => ⟨fun h0 => ⟨hoom_p, (hbrk0_fn h0).2.trans hct_o2, (hbrk0_fn h0).1⟩,
          fun h1 => ⟨hbrk1_fn h1, hoom_p⟩, by rcases hbrk_disj with rfl | rfl <;> simp⟩,
        hmbp⟩

theorem full_propagate_ignore_hot_wp (Γ : Env)
    (hOvf : ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_hot_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have har := c.harena; unfold dimacsBound at har
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have h2cv_lt31 : 2 * s.core.cur_vars < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.trail_end_le hcv_lt64
  have hpr0_lt64 : s.core.propagated < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.propagated_le hte0_lt64
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hclv_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
  have hal0_lt64 : s.core.arena_len < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.arena_len_le (Nat.lt_trans har (by decide))
  unfold Func.wp full_propagate_ignore_hot_body
  m7_hsplit
  · -- `prop >= tend`: return `0ULL` (noop)
    have hge : s.core.trail_end ≤ s.core.propagated := by
      have hh : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64] at hh
    have hpe : s.core.propagated = s.core.trail_end :=
      Nat.le_antisymm hlen0.core_ok.propagated_le hge
    exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hlen0 hw0 (.refl _) (.refl _) (Nat.le_refl _) (Or.inl rfl)
      (fun _ => ⟨hpe, rfl, fun h => h,
        fun hlt => absurd hlt (Nat.not_lt_of_ge (Nat.le_of_eq hpe.symm))⟩)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl⟩) hm0
  · -- `prop < tend`
    have hpr_lt : s.core.propagated < s.core.trail_end := by
      have hh : ¬ s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64, Nat.not_le] at hh
    m7_hsplit
    · -- `h->oom != 0`: return `2ULL`
      exact hQ 2#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hlen0 hw0 (.refl _) (.refl _) (Nat.le_refl _) (Or.inr (Or.inr rfl))
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => Or.inl hc) (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm0
    · -- `h->oom == 0`: hoist pointers/scalars and enter `while (prop < tend)`
      have hoom0 : s.core.oom = 0#64 := hc
      m7_hsteps_nogrp
      refine wp_loop_group (fun rem (prop_v, tend_v, unass_v, unfl_v, ticks_v, ()) ml =>
        M7OuterInv c F0 F_cur s R rem prop_v tend_v unass_v unfl_v ticks_v ml) ?_ ?_
      · -- Outer loop body `J`
        rintro J rem ⟨prop_v, tend_v, unass_v, unfl_v, ticks_v, ⟨⟩⟩ ml ih
          ⟨sem, te_mem, rfl, hlen_o, hw_o, htr_o, hperm_o, hag_o, hprop_eq, htend_eq,
           hunass_eq, hunfl_eq, hoom_o, hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
           hfuel_le, hfuel_lt, hpr_ge, htem_le, hpr_tem, hsc_o, hml⟩
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let sem_d : FullState :=
          { sem with core := { sem.core with propagated := s.core.propagated } }
        have hsd_len : s_disk.LengthsOk c :=
          ⟨{ hlen0.core_ok with
              trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
              propagated_le := hpr_tem },
           hlen0.scratch_ok⟩
        have hsemd_len : sem_d.LengthsOk c :=
          ⟨{ hlen_o.core_ok with
              propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
           hlen_o.scratch_ok⟩
        have hmem_len : (fastPropMem s_disk sem_d).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hsemd_len (by simp [s_disk, sem_d, hcv_o]) rfl rfl
        have hte_lt64 : sem.core.trail_end < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.trail_end_le (hcv_o ▸ hcv_lt64)
        have hpr_o_lt64 : sem.core.propagated < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.propagated_le hte_lt64
        m7_hsplit
        · -- Outer loop active (`prop_v < tend_v`)
          have hp_lt_o : prop_v.toNat < tend_v.toNat := hc
          have hp_lt_sem : sem.core.propagated < sem.core.trail_end := by
            rw [hprop_eq, htend_eq]; exact hp_lt_o
          m7_hsplit
          · -- `fl_rem == 0`: flush and return `2#64`
            have hfl0 : sem.core.fuel = 0#64 := by
              simpa [s_disk, sem_d, m7_fastPropMem_fuel] using hc
            clear ih
            m7_hsteps
            · exact m7_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
                hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
                hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
                (Or.inr (Or.inr rfl)) (fun h => absurd h (by decide)) (by decide)
                (fun _ => Or.inr hfl0)
                (by
                  simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                    hunass_eq, hunfl_eq] using hm)
            · exact m7_outer_flush_ret (ticks' := s.scratch.search_ticks)
                hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
                hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
                (Or.inr (Or.inr rfl)) (fun h => absurd h (by decide)) (by decide)
                (fun _ => Or.inr hfl0)
                (by
                  simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                    hunass_eq, hunfl_eq] using hm)
          · -- `fl_rem != 0`: consume fuel, inspect `lit = trl[prop]`
            have hfl_ne : sem.core.fuel ≠ 0#64 := by
              simpa [s_disk, sem_d, m7_fastPropMem_fuel] using hc
            have hfl_pos : 0 < sem.core.fuel.toNat := by
              by_cases h0 : sem.core.fuel.toNat = 0
              · exact absurd (BitVec.eq_of_toNat_eq h0) hfl_ne
              · omega
            have hfl_dec : (sem.core.fuel - 1#64).toNat = sem.core.fuel.toNat - 1 :=
              m7_bv64_sub_toNat (by simp; omega)
            have hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by omega
            have hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length := by
              rw [fastPropMem_trl, hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            let lit := (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl
            have hlit_eq : lit = sem.core.trl[sem.core.propagated]'(by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega) := by
              simp only [lit, fc_getElem_trl]
              exact (fc_getElem_eq_of_idx hprop_eq _ _).symm
            have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
              have := hw_o.trail_lits_lt sem.core.propagated hp_lt_sem
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              rwa [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq] at this
            let not_lit := lit ^^^ 1#32
            have hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars := by
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [fc_nat_xor_one]; split <;> omega
            have hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              refine (hw_o.vals_false_iff not_lit.toNat hnot_lt).mpr
                ⟨sem.core.propagated, hp_lt_sem, ?_⟩
              rw [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq]
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rcases Nat.mod_two_eq_zero_or_one lit.toNat with h | h
              · have h2 : (lit.toNat + 1) % 2 = 1 := by omega
                simp only [fc_nat_xor_one, h, ↓reduceIte, h2, Nat.one_ne_zero]; omega
              · have h2 : (lit.toNat - 1) % 2 = 0 := by omega
                simp only [fc_nat_xor_one, h, Nat.one_ne_zero, ↓reduceIte, h2]; omega
            have hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
              m7_bv64_shl1_u32_nat not_lit
            have hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                2 * not_lit.toNat + 1 := m7_bv64_shl1_add1_nat not_lit
            have hwv_o_len := hlen_o.core_ok.wvec_len
            have hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
              m7_bv64_add1_toNat (by have := hte_lt64; omega)
            have hnl64_lt_wv0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_1_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_lt_wv : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_lt_wv0
            have hnl64_1_lt_wv : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_1_lt_wv0
            have h_wvec_len_mem : (fastPropMem s_disk sem_d).core.wvec.length =
                4 * c.max_vars := by
              rw [fastPropMem_wvec, hwv_o_len]
            have hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length := by
              rw [hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            have hsz_hc_idx :
                ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                  (2 * ((sem.core.trl[prop_v.toNat]'hp_sem_lt_trl).toNat ^^^ 1) + 1) %
                    2 ^ 64 := by
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                simp only [lit, fc_getElem_trl, sem_d]
              have hnot_toNat : not_lit.toNat = lit.toNat ^^^ 1 := by
                dsimp only [not_lit]; rw [BitVec.toNat_xor]
                simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [hnl64_1_idx, hlit_trl, ← hnot_toNat,
                Nat.mod_eq_of_lt (by have := hlen_o.core_ok.cur_vars_le; omega)]
            m7_hsplit
            · -- `sz == 0`: advance `prop` and jump to outer loop `J`
              have hsz0 : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 = 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              m7_hsteps
              let sem_n : FullState :=
                { sem with
                  core :=
                    { sem.core with
                      propagated := prop_v.toNat + 1
                      fuel := sem.core.fuel - 1#64 } }
              have hlen_n : sem_n.LengthsOk c :=
                ⟨{ hlen_o.core_ok with propagated_le := by rw [htend_eq]; exact hp_lt_o },
                 hlen_o.scratch_ok⟩
              have hwat_n : WatchesInv F_cur sem_n.core := by
                have hw_sp : ModeWatchesInv F_cur sem_n.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_n : sem_n.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_n, ↓reduceIte] using hw_sp
              have hw_n : FullWitnessInv c F0 F_cur sem_n.core :=
                fullWitnessInv_of_nw
                  (fullWitnessInv_nw_congr hlen_n.core_ok.cur_vars_le
                    (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl)
                  (show sem_n.core.dense_mode = 0#64 from hdm_o) hwat_n
              exact ih (sem_n.core.fuel.toNat) (prop_v + 1#64, tend_v, unass_v, unfl_v,
                  ticks_v, ()) m hfl_rem_dec
                ⟨sem_n, te_mem, rfl, hlen_n, hw_n,
                  ⟨htr_o.te_ge, htr_o.trl_pref, htr_o.lvl_pres⟩,
                  hperm_o, m7_agrees_upd_prop_fuel hag_o, by simp [sem_n, hp1_prop], htend_eq,
                  hunass_eq, hunfl_eq, hoom_o,
                  hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
                  Nat.le_trans (Nat.le_of_lt hfl_rem_dec) hfuel_le,
                  fun _ => Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le,
                  by rw [hp1_prop]; omega, htem_le, hpr_tem, hsc_o, by
                    simpa [sem_n, sem_d, fastPropMem] using hm⟩
            · -- `sz > 0`: run watch loop and chrono repair
              have hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              let s_base : FullState :=
                { sem with core := { sem.core with
                  propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } }
              have hbase_len : s_base.LengthsOk c :=
                ⟨{ hlen_o.core_ok with
                    propagated_le :=
                      Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
                 hlen_o.scratch_ok⟩
              have hbase_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s_base.core) :=
                fullWitnessInv_nw_congr hbase_len.core_ok.cur_vars_le
                  (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl
              have hwat_base : WatchesInv F_cur s_base.core := by
                have hw_sp : ModeWatchesInv F_cur s_base.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_b : s_base.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_b, ↓reduceIte] using hw_sp
              have hoff0_nat : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                  hnl64_lt_wv0).setWidth 64).toNat =
                  fullWatchOffCore s_base.core not_lit.toNat := by
                unfold fullWatchOffCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_idx _)
              have hsz0_nat : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
                  fullWatchSizeCore s_base.core not_lit.toNat := by
                unfold fullWatchSizeCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_1_idx _)
              have hsz0_pos : 0 < fullWatchSizeCore s_base.core not_lit.toNat := by
                rw [← hsz0_nat]
                by_cases h0 : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                    1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat = 0
                · exact absurd (BitVec.eq_of_toNat_eq h0) hsz_ne
                · omega
              have hpi0 : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat) :=
                { len := hbase_len, nw := hbase_nw
                  sw := SplitWatchesInv.init (hcv_o ▸ hnot_lt) hwat_base hsz0_pos
                  ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl
                  not_f := by simpa [s_base] using hnot_f0 }
              m7_hsteps_nogrp
              have hm_base : (FullMem c (fastPropMem s_disk s_base) ⋆ R) m := by
                simpa only [fastPropMem, s_base, s_disk, sem_d,
                  BitVec.ofNat_eq_ofNat] using hm
              clear hm
              -- Join `t0` (`L194-197`)
              refine wp_join_group (fun (t0_v, ()) mt =>
                  (FullMem c (fastPropMem s_disk s_base) ⋆ R) mt ∧
                  (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem.core.trail_end))
                ?_ ?_
              · rintro _ ⟨t0_v, ⟨⟩⟩ mt ⟨hm_t, ht0_bound⟩
                have hend0_lt64 : fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 := by
                  have := hpi0.end_lt_wcap hnot_lt
                  exact Nat.lt_of_le_of_lt (Nat.le_trans this.1 this.2)
                    (Nat.lt_trans hwc (by decide))
                m7_hsteps_nogrp
                -- Enter `while (ovf)`: `wp_loop_break_group` (`10` vars in both `brkTs` and `lpTs`)
                refine wp_loop_break_group
                  (fun (te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, brk_b, _ovf_b, ()) mb =>
                    ∃ sem_b : FullState,
                      PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
                        p_b.toNat end_b.toNat ∧
                      te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
                      uf_b = sem_b.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
                      (brk_b = 0#64 →
                        sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
                        p_b = end_b) ∧
                      (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
                        sem_b.core.oom = 0#64) ∧
                      (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
                      (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb)
                  (fun rem_o (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, brk_o, ovf_o, ())
                      mo =>
                    ∃ sem_o : FullState,
                      rem_o = (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) ∧
                      PropLitInv c F0 F_cur s_base sem_o not_lit.toNat off_o.toNat q_o.toNat
                        p_o.toNat end_o.toNat ∧
                      te_o.toNat = sem_o.core.trail_end ∧ un_o = sem_o.core.unassigned ∧
                      uf_o = sem_o.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o.core.trail_end) ∧
                      (ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
                        sem_o.core.confl_type = s.core.confl_type) ∧
                      (ovf_o = false →
                        (brk_o = 0#64 →
                          sem_o.core.oom = 0#64 ∧ sem_o.core.confl_type = s.core.confl_type ∧
                          p_o = end_o) ∧
                        (brk_o = 1#64 → PropLitConfl F_cur ignore_ref sem_o.core ∧
                          sem_o.core.oom = 0#64) ∧
                        (brk_o = 0#64 ∨ brk_o = 1#64)) ∧
                      (FullMem c (fastPropMem s_disk sem_o) ⋆ R) mo)
                  ?_ ?_ ?_
                · -- Post-`while (ovf)`: compact tail, chrono, exit/next
                  rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, brk_b, ovf_b, ⟨⟩⟩ mb
                    ⟨sem_b, hpi_b, hte_b, hun_b, huf_b, _ht0_b, hbr0, hbr1, hbr_cases, hmb⟩
                  exact m7_compact_post_ovf_wp hChrono hQ
                    (fun sem_next te_mc mc0 hlen_n hw_n htr_n hperm_n hag_n hpr_n hte_n hun_n
                      huf_n hoom_n hct_n hdm_n hcv_n hcl_n hprob_n halen_n hfl_sem_lt hfl_s_lt
                      hfl_le hpr_ge_n htemc_le hpr_temc hsc_n hm_mc =>
                      ih sem_next.core.fuel.toNat
                        (prop_v + 1#64, te_b, un_b, uf_b, tk_b, ()) mc0 hfl_sem_lt
                        ⟨sem_next, te_mc, rfl, hlen_n, hw_n, htr_n, hperm_n, hag_n, hpr_n,
                          hte_n, hun_n, huf_n, hoom_n, hct_n, hdm_n, hcv_n, hcl_n, hprob_n,
                          halen_n, hfl_le, fun _ => hfl_s_lt, (hpr_n ▸ hpr_ge_n), htemc_le,
                          hpr_temc, hsc_n, hm_mc⟩)
                    hwc hmaxv hlen0 hpr_lt rfl ⟨te_mem, rfl, htem_le, hpr_tem⟩
                    htr_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hfl_rem_dec hfuel_le
                    hp1_prop (htend_eq ▸ hp_lt_o) hpr_ge rfl hnot_lt hdm_o hpi_b hte_b hun_b
                    huf_b (fun h => let x := hbr0 h; ⟨x.1, x.2.1⟩) hbr1 hbr_cases hmb
                · -- Body of `while (ovf)`: `ovf = false; ... while (p < end); if (ovf) { ... }`
                  rintro Bo Lo rem_o
                      ⟨te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, brk_o, ovf_o, ⟨⟩⟩
                    mo hBo ih_o ⟨sem_o, rfl, hpi_o, hte_o, hun_o, huf_o, ht0_o, hov_t, hov_f, hmo⟩
                  m7_hsplit
                  · -- `ovf_o == true`: run inner `while (p < end)` then `if (ovf)`
                    have hov_t_eq : ovf_o = true := hc
                    have ⟨hbr0_o, hoom_o2, hct_o2⟩ := hov_t hov_t_eq
                    clear hov_t hov_f hc
                    m7_hsteps_nogrp
                    -- Inner `while (p < end)` (`12` break vars) via `m7_lp_loop_wp`
                    refine wp_join_group
                      (fun (te_p, un_p, uf_p, tk_p, p_p, q_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ()) mbp =>
                        ∃ sem_p : FullState,
                          PropLitInv c F0 F_cur s_base sem_p not_lit.toNat off_o.toNat
                            q_p.toNat p_p.toNat end_o.toNat ∧
                          p_o.toNat ≤ p_p.toNat ∧ sem_o.core.trail_end ≤ sem_p.core.trail_end ∧
                          te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
                          uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
                          (ovf_p = false →
                            (brk_p = 0#64 → p_p = end_o ∧
                              sem_p.core.confl_type = sem_o.core.confl_type) ∧
                            (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
                            (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
                          (ovf_p = true →
                            brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
                            2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
                            end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
                            ovf_cr_p.toNat < 0x80000000 ∧
                            ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
                            ovf_cr_p.toNat + 3 +
                              fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
                              sem_p.core.arena_len ∧
                            ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat ≠ not_lit.toNat ∧
                            2 ≤ ovf_ri_p.toNat ∧
                            ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? =
                              some ovf_rw_p) ∧
                          (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) ?_ ?_
                    · -- Post-`while (p < end)`: handle `if (ovf)` (`L399-420`)
                      rintro _ ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ⟨⟩⟩ mbp
                        ⟨sem_p, hpi_p, _hpo_le_pp, hte_ge_p, hte_p, hun_p, huf_p, hoom_p, hnoov,
                          hov_yes, hmbp⟩
                      have ht0_p :
                          t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end :=
                        ht0_o.imp_right (fun h => Nat.le_trans h hte_ge_p)
                      dsimp only [Blocks.get]
                      change wp Γ _ _ (m7PostLpOvfExpr c _ off_o end_o Bo Lo
                        te_p un_p uf_p tk_p p_p q_p brk_p ovf_p
                        ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p) mbp
                      exact m7_post_lp_ovf_wp hOvf hBo
                        (fun n' xs m hlt => ih_o n' xs m
                          (by simpa only [hov_t_eq, ↓reduceIte] using hlt))
                        har hwc hsd_len
                        (by dsimp only [s_disk, s_base]; rw [hpi_p.cur_vars_eq, hcv_o])
                        (by simp [s_disk, s_base, hpi_p.ag.get FullCoreState.propagated])
                        (hpi_p.cur_vars_eq.symm ▸ hnot_lt)
                        hnl64_idx hct_o2 ht0_p
                        (by
                          simp only [not_lit, lit, fastPropMem_trl, fc_getElem_trl,
                            sem_d, BitVec.ofNat_eq_ofNat])
                        hpi_p _hpo_le_pp hte_p hun_p huf_p hoom_p hnoov hov_yes hmbp
                    · -- Inner `while (p < end)` body + entry via `m7_lp_loop_wp`
                      intro J_ovf hJ_ovf
                      have hnot_o : not_lit.toNat < 2 * sem_o.core.cur_vars :=
                        hpi_o.cur_vars_eq.symm ▸ hnot_lt
                      have hcl32_o : sem_o.core.cur_level < 2 ^ 32 := by
                        rw [hpi_o.ag.get FullCoreState.cur_level]
                        change sem.core.cur_level < 2 ^ 32
                        rw [hcl_o]; exact hclv_lt32
                      refine m7_lp_loop_wp c.hmaxv c.harena c.hwcap hpi_o hnot_o
                        (by
                          rw [hpi_o.cur_vars_eq]; dsimp only [s_base]; rw [hcv_o]
                          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
                          rw [Nat.mod_eq_of_lt hcv_lt64,
                            show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                            Nat.shiftLeft_eq, Nat.pow_one,
                            Nat.mul_comm s.core.cur_vars 2, Nat.mod_eq_of_lt h2cv_lt64])
                        (by
                          apply BitVec.eq_of_toNat_eq
                          rw [hpi_o.ag.get FullCoreState.cur_level]; dsimp only [s_base]
                          rw [hcl_o]
                          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hclv_lt32, Nat.mod_eq_of_lt hclv_lt64])
                        hcl32_o hte_o hun_o huf_o hoom_o2 hbr0_o hmo ?_
                      intro sem' te' un' uf' tk' p' q' brk' ovf' ovf_rw' ovf_oth' ovf_cr'
                        ovf_ri' m' hpi' hp' hte_ge' hte' hun' huf' hoom' hno' hyes' hm'
                      m7_hsteps
                      exact hJ_ovf _ m' ⟨sem', hpi', hp', hte_ge', hte', hun', huf', hoom',
                        hno', hyes', hm'⟩
                  · -- `ovf_o == false`: break out of `while (ovf)`
                    have hov_f_eq : ovf_o = false := by revert hc; cases ovf_o <;> simp
                    have ⟨h0, h1, hcs⟩ := hov_f hov_f_eq
                    exact hBo _ mo ⟨sem_o, hpi_o, hte_o, hun_o, huf_o, ht0_o, h0, h1,
                      hcs.elim Or.inl (fun h => Or.inr (Or.inl h)), hmo⟩
                · -- `while (ovf)` entry
                  intro Bo Lo hBo hLo
                  m7_hsteps
                  have hsz_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[((BitVec.setWidth 64
                          (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_add1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[((BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                        (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'
                          hnl64_1_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_1_idx.symm) pf2
                        hnl64_1_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hsz0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[(BitVec.setWidth 64 (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[(BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat]'
                        pf2).setWidth 64 =
                        (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                          hnl64_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_idx.symm) pf2
                        hnl64_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hoff0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff0_lt64 : fullWatchOffCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hend0_lt64
                  have hsz0_lt64 : fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hend0_lt64
                  have hof0_eq := m7_bv64_ofNat_toNat_lt hoff0_lt64
                  have hsz0_eq := m7_bv64_ofNat_toNat_lt hsz0_lt64
                  have hadd0_eq : (BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) +
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat)).toNat =
                      fullWatchOffCore s_base.core not_lit.toNat +
                      fullWatchSizeCore s_base.core not_lit.toNat := by
                    rw [BitVec.toNat_add, hof0_eq, hsz0_eq, Nat.mod_eq_of_lt hend0_lt64]
                  simp only [fastPropMem_wvec]
                  refine hLo (fullWatchSizeCore s_base.core not_lit.toNat + 1) _ mt ?_
                  refine ⟨s_base, ?_, ?_, htend_eq.symm, hunass_eq.symm, hunfl_eq.symm,
                    ht0_bound, fun _ => ⟨rfl, hoom_o, hct_o⟩,
                    fun h => absurd h (by decide), hm_t⟩
                  · rw [hoff_trl _ (fastPropMem_trl s_disk sem_d) _ _,
                      hsz_trl _ (fastPropMem_trl s_disk sem_d) _ _, hadd0_eq, hof0_eq]
                    simp only [↓reduceIte]
                    exact congrArg (· + 1)
                      (Nat.add_sub_cancel_left (fullWatchOffCore s_base.core not_lit.toNat)
                        (fullWatchSizeCore s_base.core not_lit.toNat)).symm
                  · rw [hoff_trl _ (fastPropMem_trl s_disk sem_d) _ _,
                      hsz_trl _ (fastPropMem_trl s_disk sem_d) _ _, hof0_eq, hadd0_eq]
                    exact hpi0
              · -- `t0` join entry (`L194-197`)
                intro Jt0 hJt0
                m7_hsplit
                · have hlit_div :
                      (((FullState.mk (fastPropMem s_disk sem_d).core
                        (fastPropMem s_disk sem_d).scratch).core.trl[prop_v.toNat]'hp_lt_trl >>>
                        (1 : Nat)).setWidth 64).toNat = lit.toNat / 2 := by
                    change ((lit >>> (1 : Nat)).setWidth 64).toNat = lit.toNat / 2
                    rw [bv_c0_zext32_64, bv32_lshr_1]
                  have hlvl_l : (fastPropMem s_disk s_base).core.lvl.length = c.max_vars := by
                    rw [fastPropMem_lvl]; exact hbase_len.core_ok.lvl_len
                  ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _));
                    c0_hfast)
                  · exact hJt0 (tend_v, ()) m ⟨hm_base, Or.inr (htend_eq ▸ Nat.le_refl _)⟩
                  · exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) m ⟨hm_base, Or.inl rfl⟩
                  · have hc' : ¬ lit.toNat < 2 * sem.core.cur_vars := by
                      have hc0 := hc
                      simp only [fastPropMem_trl] at hc0
                      rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64, ← hcv_o] at hc0
                      have hlt_eq : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                        simp only [lit, fc_getElem_trl, sem_d]
                      simpa only [hlt_eq] using hc0
                    exact absurd hlit_lt hc'
                · m7_hsteps; exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) m ⟨hm_base, Or.inl rfl⟩
        · -- Outer loop exits (`!(prop < tend)`): flush and return `0#64`
          have hpe_o : sem.core.propagated = sem.core.trail_end := by
            have hh : tend_v.toNat ≤ prop_v.toNat := Nat.le_of_not_lt hc
            rw [← htend_eq, ← hprop_eq] at hh
            exact Nat.le_antisymm hlen_o.core_ok.propagated_le hh
          have hprop_gt : s.core.propagated < prop_v.toNat := by
            rw [← hprop_eq, hpe_o]
            exact Nat.lt_of_lt_of_le hpr_lt htr_o.te_ge
          have hfuel_dec := hfuel_lt hprop_gt
          clear ih
          m7_hsteps
          · exact m7_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
              hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
              hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
              (Or.inl rfl)
              (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o,
                fun _ => hfuel_dec⟩)
              (by decide) (fun h => absurd h (by decide))
              (by
                simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                  hunass_eq, hunfl_eq] using hm)
          · exact m7_outer_flush_ret (ticks' := s.scratch.search_ticks)
              hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
              hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
              (Or.inl rfl)
              (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o,
                fun _ => hfuel_dec⟩)
              (by decide) (fun h => absurd h (by decide))
              (by
                simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                  hunass_eq, hunfl_eq] using hm)
      · -- Entry to outer `while (prop < tend)`
        intro J hJ
        exact hJ s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated,
            BitVec.ofNat 64 s.core.trail_end, s.core.unassigned, s.core.unflushed, 0#64, ()) m
          ⟨s, s.core.trail_end, rfl, hlen0, hw0, .refl _, .refl _, .refl _ _,
            (m7_bv64_ofNat_toNat_lt hpr0_lt64).symm, (m7_bv64_ofNat_toNat_lt hte0_lt64).symm,
            rfl, rfl, hoom0, rfl, hdense0, rfl, rfl, rfl, rfl, Nat.le_refl _,
            fun hlt => absurd (m7_bv64_ofNat_toNat_lt hpr0_lt64 ▸ hlt) (Nat.lt_irrefl _),
            by rw [m7_bv64_ofNat_toNat_lt hpr0_lt64]; exact Nat.le_refl _,
            Nat.le_refl _, hlen0.core_ok.propagated_le,
            rfl, by simpa only [fastPropMem_self] using hm0⟩

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
