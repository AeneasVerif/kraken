/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpWatchHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpFlushHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfFlush
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerBin
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerLarge
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerLoop
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpPost
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import Lean.Elab.Tactic
meta import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Canonical Overflow-Tail & `while (ovf)` Loop WP Proofs (`PropSearch.WpOvfTail`)

Plain `public section` (`@[expose]` ONLY on concrete AST `Expr` builders, `0` `@[expose]` on
theorems/lemmas, `0` legacy imports, `<= 100` cols, every theorem `<= 380` lines):
1. `s13OvfTailExpr`, `s13_ovf_ok_step`, `s13_ovf_tail_wp`: post-scan delayed-watch flush +
   cold `full_prop_lit_ovf_hot` + `wvec[nl64]` rebase + `[0]/[1]` arena swap / fail-keep.
2. `s13LoSig`, `s13LoJump`, `s13PostLpOvfExpr`, `s13LoTup`, `s13OvfTup`, `s13_post_lp_ovf_wp`. -/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.PropSearch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropTactics

private theorem fastPropMem_def (s0 sem : FullState) :
    fastPropMem s0 sem =
      { core :=
          { s0.core with
            cur_vars := sem.core.cur_vars, arena_len := sem.core.arena_len,
            wlen := sem.core.wlen, wusable := sem.core.wusable, probing := sem.core.probing,
            propagated := sem.core.propagated, cur_level := sem.core.cur_level,
            fuel := sem.core.fuel, confl_ref := sem.core.confl_ref,
            confl_type := sem.core.confl_type, confl_lit0 := sem.core.confl_lit0,
            confl_lit1 := sem.core.confl_lit1, oom := sem.core.oom,
            vals := sem.core.vals, flags := sem.core.flags, lvl := sem.core.lvl,
            rsns := sem.core.rsns, trl := sem.core.trl, trail_pos := sem.core.trail_pos,
            wvec := sem.core.wvec, arena := sem.core.arena, wstk := sem.core.wstk }
        scratch :=
          { s0.scratch with
            delayed_len := sem.scratch.delayed_len, search_ticks := sem.scratch.search_ticks,
            phases := sem.scratch.phases, wsort := sem.scratch.wsort,
            delayed := sem.scratch.delayed } } := rfl

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. `while (ovf)` Jump Signature & Post-Scan Overflow AST Builders -/

/-- Step-13 `while (ovf)` header signature (`10` args when `isBeyond = true`, `11` when `false`). -/
abbrev s13LoSig (isBeyond : Bool) : List Ty :=
  if isBeyond then [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]
  else [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]

/-- Step-13 `while (ovf)` jump (`brk` omitted when `isBeyond = true`). -/
abbrev s13LoJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (Lo : L (s13LoSig isBeyond))
    (te un uf tk off p q ed di brk : Arg V i64) (ovf : Arg V Ty.bool) : Expr V L rs :=
  match isBeyond, Lo with
  | true, L0 => Expr.jump L0 (te, un, uf, tk, off, p, q, ed, di, ovf, ())
  | false, L0 => Expr.jump L0 (te, un, uf, tk, off, p, q, ed, di, brk, ovf, ())

/-- Rebase + arena-swap (`pk = true`) or keep-watch-and-break (`pk = false`) overflow tail. -/
@[expose] def s13OvfTailExpr (isBeyond : Bool) (c : FullCfg) (nl64 : Val i64)
    (not_lit_v : Val i32) (off_o end_o : Val i64)
    (Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (Js0 : Cont [i64, i64, i64, i64, i64, i64])
    (te_p un_p uf_p tk_p p_p q_p di_f brk_p : Val i64) (ovf_p pk : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ ⟨OpCode.mul i64, (Arg.var nl64, Arg.imm 4, ())⟩ fun boff =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWvec, Arg.var boff.fst, ())⟩ fun addr =>
  Expr.load i32 (Arg.var addr.fst) fun noff32 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noff32, ())⟩ fun noff =>
  Expr.group (sig := [[i64, i64, i64, i64]])
    (fun _Jn => Blocks.cons
      (fun pn =>
        Expr.jnz (Arg.var pk)
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
          Expr.jump Js0
            (Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var pn.snd.snd.fst,
              Arg.var pn.snd.snd.snd.fst, Arg.var di_f,
              if isBeyond then Arg.imm 0 else Arg.var brk_p, ()))
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
              Arg.var pn.snd.snd.snd.fst, Arg.var di_f, Arg.imm 2,
              Arg.var ovf_p, ())))
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
          (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, ())))

/-- Step-13 post-scan overflow handler parameterized over `isBeyond`. -/
@[expose] def s13PostLpOvfExpr (isBeyond : Bool) (c : FullCfg) (nl64 : Val i64)
    (not_lit_v : Val i32) (off_o end_o : Val i64)
    (Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (Lo : Cont (s13LoSig isBeyond))
    (te_p un_p uf_p tk_p p_p q_p di_p brk_p : Val i64) (ovf_p : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64]])
    (fun _Js0 => Blocks.cons
      (fun p1 => s13LoJump isBeyond Lo (Arg.var te_p) (Arg.var un_p) (Arg.var uf_p)
        (Arg.var tk_p) (Arg.var p1.fst) (Arg.var p1.snd.fst) (Arg.var p1.snd.snd.fst)
        (Arg.var p1.snd.snd.snd.fst) (Arg.var p1.snd.snd.snd.snd.fst)
        (Arg.var p1.snd.snd.snd.snd.snd.fst) (Arg.var ovf_p))
      Blocks.nil)
    (fun Js0 =>
      Expr.jnz (Arg.var ovf_p)
        (Expr.group (sig := [[i64, Ty.bool]])
          (fun _Jf => Blocks.cons
            (fun fok =>
              Expr.group (sig := [[Ty.bool]])
                (fun _Jp => Blocks.cons
                  (fun pk =>
                    s13OvfTailExpr isBeyond c nl64 not_lit_v off_o end_o Bo Js0.fst
                      te_p un_p uf_p tk_p p_p q_p fok.fst brk_p ovf_p pk.fst
                      ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p)
                  Blocks.nil)
                (fun Jp =>
                  Expr.jnz (Arg.var fok.snd.fst)
                    (@Expr.call _ _ [i64] "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool]
                      (Arg.var c.hdr, Arg.var ovf_rw_p, Arg.var ovf_oth_p, Arg.var ovf_cr_p, ())
                      fun pok => Expr.jump Jp.fst (Arg.var pok.fst, ()))
                    (Expr.jump Jp.fst (Arg.imm false, ()))))
            Blocks.nil)
          (fun Jf =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var di_p, Arg.imm 0, ())⟩ fun hc =>
            Expr.jnz (Arg.var hc.fst)
              (@Expr.call _ _ [i64] "full_prop_flush_del_fid" [i64, i64] [.bool]
                (Arg.var c.hdr, Arg.var di_p, ()) fun ok =>
                Expr.jump Jf.fst (Arg.imm 0, Arg.var ok.fst, ()))
              (Expr.jump Jf.fst (Arg.var di_p, Arg.imm true, ()))))
        (Expr.jump Js0.fst (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o,
          Arg.var di_p, if isBeyond = true then Arg.imm 0 else Arg.var brk_p, ())))

/-! ## 2. Overflow Rebase + Arena-Swap / Fail-Keep WP Proofs -/

private theorem s13_ovf_pi4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem2 st4 : FullState} {not_lit other repl cref : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {pok : Bool}
    (hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen4 : st4.LengthsOk c) (hcv4 : st4.core.cur_vars = sem2.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem2.core.cur_vars) (hlay4 : WatchStackLayout st4.core)
    (hperm24 : FullArenaPermEq sem2.core st4.core)
    (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hag4 : AgreesExcept propLitCoreMask s_pi.core st4.core)
    (htr4 : FullTrailExt s_pi.core st4.core) (hrsns4 : FullTrailRsnsPres s_pi.core st4.core)
    (hsc4 : st4.scratch = { s_pi.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hrepl_lt : repl.toNat < 2 * sem2.core.cur_vars) (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hother_pres : ∀ l < 2 * sem2.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore sem2.core l ∧
      ∀ k < fullWatchSizeCore sem2.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core l + k]?)
    (hpok_t : pok = true →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore sem2.core repl.toNat + 2 ∧
      (∀ k < fullWatchSizeCore sem2.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core repl.toNat + k]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat]? = some (other &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore sem2.core repl.toNat ∧
      ∀ k < fullWatchSizeCore sem2.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core repl.toNat + k]?) :
    let off4_v := (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    let p4_v := off4_v + (p_v + 1#64 + 1#64 - off_v)
    let end4_v := off4_v + (end_v - off_v)
    off4_v.toNat = fullWatchOffCore st4.core not_lit.toNat ∧
      q4_v.toNat = off4_v.toNat + (q_v.toNat - off_v.toNat) ∧
      p4_v.toNat = off4_v.toNat + (p_v.toNat + 2 - off_v.toNat) ∧
      end4_v.toNat = off4_v.toNat + (end_v.toNat - off_v.toNat) ∧
      q4_v.toNat + 2 ≤ p4_v.toNat ∧ p4_v.toNat ≤ end4_v.toNat ∧
      PropLitInv c F0 F_cur s_pi st4 not_lit.toNat off4_v.toNat q4_v.toNat
        p4_v.toNat end4_v.toNat := by
  intro off4_v q4_v p4_v end4_v
  have hxor1 : (not_lit ^^^ 1#32) ^^^ 1#32 = not_lit := by
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have hsw4_prep := propLit_b1_after_push (c := c) (F_cur := F_cur) (st3 := sem2) (st4 := st4)
    (lit := not_lit ^^^ 1#32) (other := other) (cref := cref) (repl := repl)
    (off_v := off_v) (p_v := p_v) (q_v := q_v) (end_v := end_v) (pok := pok)
    (idx0 := 2 * not_lit.toNat) (by rw [hxor1]; exact hnot_lt) hcv4
    (by rw [hxor1, hcv4]; exact hnot_lt) hlen4 hlay4 (by rw [hxor1]; exact hpi2.sw)
    hperm24.2.1 hrepl_lt (by rw [hxor1]; exact hrepl_ne) hcr_lt hcr_ref2 hp2_nat hq_le
    hother_pres hpok_t hpok_f (by rw [hxor1])
  rw [hxor1] at hsw4_prep
  rcases hsw4_prep with ⟨hoff4_n, hq4_n, hp4_n, hend4_n, hq4_p4, hp4_end4, _, hsw4⟩
  exact ⟨hoff4_n, hq4_n, hp4_n, hend4_n, hq4_p4, hp4_end4,
    { len := hlen4, nw := hnw4, sw := hsw4, ag := hag4, tr := htr4, rsns_pres := hrsns4
      perm := fullArenaPermEq_trans hpi2.perm hperm24, sc_eq := hsc4, not_f := hnot_f4 }⟩

private theorem s13_ovf_ok_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem2 st4 : FullState} {not_lit other repl cref : BitVec 32}
    {ri_n : Nat} {off_v p_v q_v end_v : BitVec 64}
    (hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen4 : st4.LengthsOk c) (hcv4 : st4.core.cur_vars = sem2.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem2.core.cur_vars) (hlay4 : WatchStackLayout st4.core)
    (hperm24 : FullArenaPermEq sem2.core st4.core)
    (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hag4 : AgreesExcept propLitCoreMask s_pi.core st4.core)
    (htr4 : FullTrailExt s_pi.core st4.core)
    (hrsns4 : FullTrailRsnsPres s_pi.core st4.core)
    (hsc4 : st4.scratch = { s_pi.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (har4_eq : st4.core.arena = sem2.core.arena)
    (har_fit2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤ sem2.core.arena_len)
    (hal_4 : st4.core.arena_len = sem2.core.arena_len)
    {l0' l1' : BitVec 32} (hwt : l0' = not_lit ∨ l1' = not_lit)
    (hoth_xor : other = l0' ^^^ l1' ^^^ not_lit)
    (har3 : sem2.core.arena[cref.toNat + 3]? = some l0')
    (har4 : sem2.core.arena[cref.toNat + 4]? = some l1')
    (hri2 : 2 ≤ ri_n) (hri_lt2 : ri_n < fullArenaClauseSizeCore sem2.core cref.toNat)
    (har_ri : sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl)
    (hrepl_lt : repl.toNat < 2 * sem2.core.cur_vars) (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hother_pres : ∀ l < 2 * sem2.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore sem2.core l ∧
      ∀ k < fullWatchSizeCore sem2.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core l + k]?)
    (hrepl_ok : fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore sem2.core repl.toNat + 2 ∧
      (∀ k < fullWatchSizeCore sem2.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core repl.toNat + k]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat]? = some (other &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat + 1]? = some cref) :
    let off4_v := st4.core.wvec[2 * not_lit.toNat]?.getD 0#32 |>.setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    let p4_v := off4_v + (p_v + 1#64 + 1#64 - off_v)
    let end4_v := off4_v + (end_v - off_v)
    let st5 : FullState :=
      { st4 with core := { st4.core with
          arena := ((st4.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
            (cref.toNat + 3 + ri_n) not_lit } }
    PropLitInv c F0 F_cur s_pi st5 not_lit.toNat off4_v.toNat q4_v.toNat p4_v.toNat
      end4_v.toNat := by
  intro off4_v q4_v p4_v end4_v st5
  obtain ⟨_, _, hp4_n, _, _, _, hpi4⟩ := s13_ovf_pi4 (pok := true) hpi2 hlen4 hcv4 hnot_lt hlay4
    hperm24 hnw4 hag4 htr4 hrsns4 hsc4 hnot_f4 hrepl_lt hrepl_ne hcr_lt hcr_ref2 hp2_nat hq_le
    hother_pres (fun _ => hrepl_ok) (fun h => by cases h)
  have hp4_2 : 2 ≤ p4_v.toNat := by
    have := hpi2.sw.q_ge; have := hpi2.sw.q_le_p; have := hpi2.sw.p_le_end
    change 2 ≤ (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
    rw [hp4_n]; omega
  have hp4_sub2 : (p4_v - 2#64).toNat + 2 = p4_v.toNat := by
    rw [m7_bv64_sub_toNat (by simpa using hp4_2), show (2#64 : BitVec 64).toNat = 2 from rfl]
    omega
  have hcr_ref4 : cref.toNat ∈ fullArenaClauseRefsCore st4.core := hperm24.2.1 ▸ hcr_ref2
  have hcsz4_eq : fullArenaClauseSizeCore st4.core cref.toNat =
      fullArenaClauseSizeCore sem2.core cref.toNat := (hperm24.2.2 cref.toNat hcr_ref2).1
  have hcsz3_4 : 3 ≤ fullArenaClauseSizeCore st4.core cref.toNat :=
    (hnw4.arena.refs_wf cref.toNat hcr_ref4).2.1
  have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
      st4.core.arena_len := by rw [hal_4, hcsz4_eq]; exact har_fit2
  have hri_lt4 : ri_n < fullArenaClauseSizeCore st4.core cref.toNat := hcsz4_eq ▸ hri_lt2
  have haren := hlen4.core_ok.arena_len_arr; have halen := hlen4.core_ok.arena_len_le
  have har3_4 : st4.core.arena[cref.toNat + 3]? = some l0' := har4_eq.symm ▸ har3
  have har4_4 : st4.core.arena[cref.toNat + 4]? = some l1' := har4_eq.symm ▸ har4
  have har_ri4 : st4.core.arena[cref.toNat + 3 + ri_n]? = some repl := har4_eq.symm ▸ har_ri
  have h1_ri : st4.core.arena[cref.toNat + 3 + ri_n]'(by omega) = repl := by
    rw [List.getElem?_eq_getElem (by omega)] at har_ri4; exact Option.some.inj har_ri4
  have h1_4 : st4.core.arena[cref.toNat + 3 + 1]'(by omega) = l1' := by
    rw [List.getElem?_eq_getElem (by omega)] at har4_4; exact Option.some.inj har4_4
  rcases hwt with hl0 | hl1
  · have hoth_eq : other = l1' := by
      rw [hoth_xor, hl0, BitVec.xor_comm not_lit l1', BitVec.xor_assoc, BitVec.xor_self,
        BitVec.xor_zero]
    have h1_3 : st4.core.arena[cref.toNat + 3 + 0]'(by omega) = l0' := by
      rw [Nat.add_zero, List.getElem?_eq_getElem (by omega)] at har3_4
      exact Option.some.inj har3_4
    have ⟨hnw_a, hperm_a⟩ := full_swapLits_preserves_nw hlen4.core_ok hnw4 hcr_ref4
      (k1 := 0) (k2 := 1) (by omega) (by omega)
    let ar_a := (st4.core.arena.set (cref.toNat + 3 + 0)
      (st4.core.arena[cref.toNat + 3 + 1]'(by omega))).set (cref.toNat + 3 + 1)
      (st4.core.arena[cref.toNat + 3 + 0]'(by omega))
    let st_a : FullState := { st4 with core := { st4.core with arena := ar_a } }
    have hlen_a : st_a.core.LengthsOk c :=
      { hlen4.core_ok with arena_len_arr := by simp [st_a, ar_a, haren] }
    have hcr_ref_a : cref.toNat ∈ fullArenaClauseRefsCore st_a.core := hperm_a.2.1 ▸ hcr_ref4
    have hri_lt_a : ri_n < fullArenaClauseSizeCore st_a.core cref.toNat := by
      rw [(hperm_a.2.2 cref.toNat hcr_ref4).1]; exact hri_lt4
    have ⟨hnw_b, hperm_b⟩ := full_swapLits_preserves_nw hlen_a hnw_a hcr_ref_a
      (k1 := 1) (k2 := ri_n) (by omega) hri_lt_a
    have har_eq_fin :
        (ar_a.set (cref.toNat + 3 + 1) (ar_a[cref.toNat + 3 + ri_n]'(by
          simp only [ar_a, List.length_set]; omega))).set (cref.toNat + 3 + ri_n)
          (ar_a[cref.toNat + 3 + 1]'(by simp only [ar_a, List.length_set]; omega)) =
        st5.core.arena := by
      have har_a_len : ar_a.length = st4.core.arena.length := by simp [ar_a]
      apply List.ext_getElem (by simp [st5, ar_a])
      intro i hi1 hi2
      have hri_ne30 : cref.toNat + 3 + 0 ≠ cref.toNat + 3 + ri_n := by omega
      have hri_ne31 : cref.toNat + 3 + 1 ≠ cref.toNat + 3 + ri_n := by omega
      have har_a31 : ar_a[cref.toNat + 3 + 1]'(by rw [har_a_len]; omega) = not_lit := by
        simp [ar_a, h1_3, hl0]
      have har_ari : ar_a[cref.toNat + 3 + ri_n]'(by rw [har_a_len]; omega) = repl := by
        dsimp only [ar_a]
        rw [List.getElem_set_ne hri_ne31, List.getElem_set_ne hri_ne30, h1_ri]
      simp only [st5, har_a31, har_ari, List.getElem_set]
      by_cases hri : cref.toNat + 3 + ri_n = i
      · simp [hri]
      · simp only [hri, ↓reduceIte]
        by_cases h4 : cref.toNat + 4 = i
        · simp [h4]
        · simp only [h4, ↓reduceIte]
          by_cases h3 : cref.toNat + 3 = i
          · simp only [h3, ↓reduceIte]
            have hidx0 : i = cref.toNat + 3 + 0 := by omega
            subst hidx0
            dsimp only [ar_a]
            rw [List.getElem_set_ne (by omega), List.getElem_set_self, h1_4, hoth_eq]
          · simp only [h3, ↓reduceIte, ar_a]
            rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
    rw [har_eq_fin] at hperm_b hnw_b
    have hperm_ab : FullArenaPermEq st4.core st5.core := fullArenaPermEq_trans hperm_a hperm_b
    have hnw_s : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st5.core) := hnw_b
    exact
      { len := ⟨{ hlen4.core_ok with arena_len_arr := by simp [st5, haren] }, hlen4.scratch_ok⟩
        nw := hnw_s
        sw := SplitWatchesInv.with_nonwatch hpi4.sw rfl rfl rfl rfl (fun _ r => hperm_ab.2.1 ▸ r)
        ag := hpi4.ag.update (fun k => { k with arena := st5.core.arena })
        tr := fullTrailExt_congr hpi4.tr rfl rfl rfl
        rsns_pres := fullTrailRsnsPres_congr hpi4.rsns_pres rfl
        perm := fullArenaPermEq_trans hpi4.perm hperm_ab, sc_eq := hpi4.sc_eq,
        not_f := hpi4.not_f }
  · have hoth_eq : other = l0' := by
      rw [hoth_xor, hl1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    have ⟨hnw_s, hperm_s⟩ := full_swapLits_preserves_nw hlen4.core_ok hnw4 hcr_ref4
      (k1 := 1) (k2 := ri_n) (by omega) hri_lt4
    have hset3 : (st4.core.arena.set (cref.toNat + 3) other) = st4.core.arena :=
      hoth_eq ▸ m7_list_set_eq_self har3_4
    have hst5_eq : st5.core =
        { st4.core with
          arena := (st4.core.arena.set (cref.toNat + 3 + 1)
            (st4.core.arena[cref.toNat + 3 + ri_n]'(by omega))).set (cref.toNat + 3 + ri_n)
            (st4.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
      simp only [st5, hset3, h1_4, h1_ri, hl1, show cref.toNat + 3 + 1 = cref.toNat + 4 by omega]
    rw [← hst5_eq] at hnw_s hperm_s
    exact
      { len := ⟨{ hlen4.core_ok with arena_len_arr := by simp [st5, haren] }, hlen4.scratch_ok⟩
        nw := hnw_s
        sw := SplitWatchesInv.with_nonwatch hpi4.sw rfl rfl rfl rfl (fun _ r => hperm_s.2.1 ▸ r)
        ag := hpi4.ag.update (fun k => { k with arena := st5.core.arena })
        tr := fullTrailExt_congr hpi4.tr rfl rfl rfl
        rsns_pres := fullTrailRsnsPres_congr hpi4.rsns_pres rfl
        perm := fullArenaPermEq_trans hpi4.perm hperm_s, sc_eq := hpi4.sc_eq, not_f := hpi4.not_f }

private theorem s13_ovf_tail_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk s_base sem_o sem_p sem_f st4 : FullState}
    {not_lit ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32}
    {off_o end_o p_p q_p te_p un_p uf_p tk_p di_f brk_p ovf_ri_p : BitVec 64} {pk : Bool}
    {Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    {Js0 : Cont [i64, i64, i64, i64, i64, i64]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m4 : Mem 64}
    (har : c.arena_cap < 2 * dimacsBound) (hwc : c.wcap < 2 * dimacsBound)
    (hnot_lt : not_lit.toNat < 2 * sem_p.core.cur_vars)
    (hoff_o : off_o.toNat = fullWatchOffCore sem_p.core not_lit.toNat)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = s_base.core.cur_vars)
    (hsd_pr : s_disk.core.propagated = s_base.core.propagated)
    (hd0_p : c.delayed_cap = 0 → sem_p.scratch.delayed = s_orig.scratch.delayed)
    (hpi_p : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
      sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat)
    (hp_off2 : 2 ≤ p_p.toNat - off_o.toNat) (hq_pp2 : q_p.toNat + 2 ≤ p_p.toNat)
    (hcr_lt : ovf_cr_p.toNat < 0x80000000)
    (hcr_ref : ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core)
    (hcr_fit : ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
      sem_p.core.arena_len)
    (_hoth_lt : ovf_oth_p.toNat < 2 * sem_p.core.cur_vars)
    (hovf_lt : ovf_rw_p.toNat < 2 * sem_p.core.cur_vars) (hovf_ne : ovf_rw_p.toNat ≠ not_lit.toNat)
    (hri2 : 2 ≤ ovf_ri_p.toNat)
    (hri_lt : ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat)
    (hwt_p : ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧
      ovf_oth_p = l0' ^^^ l1' ^^^ not_lit ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3]? = some l0' ∧
      sem_p.core.arena[ovf_cr_p.toNat + 4]? = some l1')
    (har_ri : sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hct_p : S13ConflEq sem_o.core sem_p.core)
    (hoom_p : sem_p.core.oom = 0#64) (hbrk_p : brk_p = 0#64)
    (hlen_f : sem_f.LengthsOk c) (_hlay_f : WatchStackLayout sem_f.core)
    (hnw_f : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem_f.core))
    (hag_f : AgreesExcept propLitCoreMask s_base.core sem_f.core)
    (htr_f : FullTrailExt s_base.core sem_f.core)
    (hrsns_f : FullTrailRsnsPres s_base.core sem_f.core)
    (hperm_f : FullArenaPermEq s_base.core sem_f.core)
    (hcv_f : sem_f.core.cur_vars = sem_p.core.cur_vars)
    (hvals_f : sem_f.core.vals = sem_p.core.vals)
    (har_f : sem_f.core.arena = sem_p.core.arena)
    (halen_f : sem_f.core.arena_len = sem_p.core.arena_len)
    (hsc_f : sem_f.scratch = { { s_base with scratch := { s_base.scratch with
        delayed := sem_p.scratch.delayed } }.scratch with
      search_ticks := sem_f.scratch.search_ticks, wsort := sem_f.scratch.wsort,
      phases := sem_f.scratch.phases })
    (hsw_f : let off_f := fullWatchOffCore sem_f.core not_lit.toNat
      SplitWatchesInv F_cur sem_f.core not_lit.toNat off_f
        (off_f + (q_p.toNat - off_o.toNat)) (off_f + (p_p.toNat - off_o.toNat))
        (off_f + (end_o.toNat - off_o.toNat)))
    (hlen4 : st4.LengthsOk c) (hlay4 : WatchStackLayout st4.core)
    (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hag4 : AgreesExcept propLitCoreMask s_base.core st4.core)
    (htr4 : FullTrailExt s_base.core st4.core)
    (hrsns4 : FullTrailRsnsPres s_base.core st4.core)
    (hperm24 : FullArenaPermEq sem_f.core st4.core)
    (hcv4 : st4.core.cur_vars = sem_f.core.cur_vars) (hvals4 : st4.core.vals = sem_f.core.vals)
    (har4_eq : st4.core.arena = sem_f.core.arena) (hal4 : st4.core.arena_len = sem_f.core.arena_len)
    (hte4 : st4.core.trail_end = sem_p.core.trail_end)
    (hun4 : st4.core.unassigned = sem_p.core.unassigned)
    (huf4 : st4.core.unflushed = sem_p.core.unflushed) (hoom4 : st4.core.oom = sem_p.core.oom)
    (hct4 : S13ConflEq sem_p.core st4.core)
    (hsc4 : st4.scratch = { { s_base with scratch := { s_base.scratch with
        delayed := sem_p.scratch.delayed } }.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hdel4 : st4.scratch.delayed = sem_p.scratch.delayed)
    (hoth_pr : ∀ l < 2 * sem_f.core.cur_vars, l ≠ ovf_rw_p.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore sem_f.core l ∧
      ∀ k < fullWatchSizeCore sem_f.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          sem_f.core.wstk[fullWatchOffCore sem_f.core l + k]?)
    (hpok_t_pr : pk = true →
      fullWatchSizeCore st4.core ovf_rw_p.toNat = fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 2 ∧
      (∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
        st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
          sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
        fullWatchSizeCore sem_f.core ovf_rw_p.toNat]? = some (ovf_oth_p &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
        fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 1]? = some ovf_cr_p)
    (hpok_f_pr : pk = false →
      fullWatchSizeCore st4.core ovf_rw_p.toNat = fullWatchSizeCore sem_f.core ovf_rw_p.toNat ∧
      ∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
        st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
          sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?)
    (hte_p : te_p.toNat = sem_p.core.trail_end) (hun_p : un_p = sem_p.core.unassigned)
    (huf_p : uf_p = sem_p.core.unflushed)
    (hm4 : (FullMem c (fastPropMem s_disk st4) ⋆ R) m4)
    (hJs0 : ∀ x mj,
      (∃ sem_n : FullState,
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_n.scratch.delayed } }
          sem_n not_lit.toNat x.1.toNat x.2.2.1.toNat x.2.1.toNat x.2.2.2.1.toNat ∧
        (c.delayed_cap = 0 → sem_n.scratch.delayed = s_orig.scratch.delayed) ∧
        te_p.toNat = sem_n.core.trail_end ∧ un_p = sem_n.core.unassigned ∧
        uf_p = sem_n.core.unflushed ∧ sem_n.core.oom = 0#64 ∧
        S13ConflEq sem_o.core sem_n.core ∧
        x.2.2.2.2.1 = 0#64 ∧ x.2.2.2.2.2.1 = 0#64 ∧
        x.2.2.2.2.1.toNat = 0 ∧ x.2.2.2.1.toNat - x.2.1.toNat = end_o.toNat - p_p.toNat ∧
        (x.2.2.2.2.2.1 = 0#64 → sem_n.core.oom = 0#64 ∧
          S13ConflEq sem_o.core sem_n.core) ∧
        (FullMem c (fastPropMem s_disk sem_n) ⋆ R) mj) →
      Js0 x mj)
    (hBo : ∀ x mb,
      (∃ sem_b : FullState,
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
          sem_b not_lit.toNat x.2.2.2.2.1.toNat x.2.2.2.2.2.2.1.toNat
          x.2.2.2.2.2.1.toNat x.2.2.2.2.2.2.2.1.toNat ∧
        x.2.2.2.2.2.2.2.2.1 = 0#64 ∧
        (c.delayed_cap = 0 → sem_b.scratch.delayed = s_orig.scratch.delayed) ∧
        x.1.toNat = sem_b.core.trail_end ∧ x.2.1 = sem_b.core.unassigned ∧
        x.2.2.1 = sem_b.core.unflushed ∧ x.2.2.2.2.2.2.2.2.2.1 = 2#64 ∧
        S13ConflEq sem_o.core sem_b.core ∧
        (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) →
      Bo x mb)
    (hdi_f : di_f = 0#64) :
    wp Γ Q X (s13OvfTailExpr isBeyond c (not_lit.setWidth 64 <<< (1 : Nat)) not_lit off_o end_o
      Bo Js0 te_p un_p uf_p tk_p p_p q_p di_f brk_p true pk ovf_rw_p ovf_oth_p ovf_cr_p
      ovf_ri_p) m4 := by
  unfold dimacsBound at har hwc; subst hbrk_p hdi_f
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hnot_f : not_lit.toNat < 2 * sem_f.core.cur_vars := hcv_f.symm ▸ hnot_lt
  have hcv4_p : st4.core.cur_vars = sem_p.core.cur_vars := hcv4.trans hcv_f
  have hnot4 : not_lit.toNat < 2 * st4.core.cur_vars := hcv4.symm ▸ hnot_f
  have hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
    rw [hvals4, hvals_f]; exact hpi_p.not_f
  let s_pi_p : FullState :=
    { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
  have hpi_f : PropLitInv c F0 F_cur s_pi_p sem_f not_lit.toNat
      (fullWatchOffCore sem_f.core not_lit.toNat)
      (fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat))
      (fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat))
      (fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat)) :=
    { len := hlen_f, nw := hnw_f, sw := hsw_f, ag := hag_f, tr := htr_f, rsns_pres := hrsns_f
      perm := hperm_f, sc_eq := hsc_f, not_f := by rw [hvals_f]; exact hpi_p.not_f }
  have hoff_f_lt64 : fullWatchOffCore sem_f.core not_lit.toNat < 2 ^ 64 := by
    have := hsw_f.layout.bounds not_lit.toNat hnot_f; have := hlen_f.core_ok.wlen_le; omega
  have hend_f_le : fullWatchOffCore sem_f.core not_lit.toNat +
      (end_o.toNat - off_o.toNat) ≤ c.wcap := by
    have := hsw_f.layout.bounds not_lit.toNat hnot_f
    rw [hsw_f.off_eq, hsw_f.sz_eq] at this
    have := hlen_f.core_ok.wlen_le; have := hsw_f.q_ge; have := hsw_f.q_le_p
    have := hsw_f.p_le_end; omega
  let off_f_v := BitVec.ofNat 64 (fullWatchOffCore sem_f.core not_lit.toNat)
  let q_f_v := off_f_v + (q_p - off_o)
  let p_f_v := off_f_v + (p_p - off_o)
  let end_f_v := off_f_v + (end_o - off_o)
  have hq_ge_o := hpi_p.sw.q_ge; have hq_le_o := hpi_p.sw.q_le_p; have hp_le_o := hpi_p.sw.p_le_end
  have hoff_fv_n : off_f_v.toNat = fullWatchOffCore sem_f.core not_lit.toNat :=
    m7_bv64_ofNat_toNat_lt hoff_f_lt64
  have hqf_n : q_f_v.toNat =
      fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat) := by
    dsimp only [q_f_v]; rw [BitVec.toNat_add, hoff_fv_n, m7_bv64_sub_toNat hq_ge_o,
      Nat.mod_eq_of_lt (by omega)]
  have hpf_n : p_f_v.toNat =
      fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat) := by
    dsimp only [p_f_v]; rw [BitVec.toNat_add, hoff_fv_n,
      m7_bv64_sub_toNat (Nat.le_trans hq_ge_o hq_le_o), Nat.mod_eq_of_lt (by omega)]
  have hendf_n : end_f_v.toNat =
      fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat) := by
    dsimp only [end_f_v]; rw [BitVec.toNat_add, hoff_fv_n,
      m7_bv64_sub_toNat (Nat.le_trans (Nat.le_trans hq_ge_o hq_le_o) hp_le_o),
      Nat.mod_eq_of_lt (by omega)]
  have hpf_ge2 : (2#64 : BitVec 64).toNat ≤ p_f_v.toNat := by change 2 ≤ p_f_v.toNat; omega
  have h2_64 : (2#64 : BitVec 64).toNat = 2 := rfl
  have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hpv_sub2 : (p_f_v - 2#64).toNat + 2 = p_f_v.toNat := by
    rw [m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
  have hpf_back : (p_f_v - 2#64) + 1#64 + 1#64 = p_f_v := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (p_f_v - 2#64).toNat + 1 < 2 ^ 64 := by rw [m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
    rw [BitVec.toNat_add, BitVec.toNat_add, m7_bv64_sub_toNat hpf_ge2, h2_64, h1_64,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hpf_back_nat : ((p_f_v - 2#64) + 1#64 + 1#64).toNat = (p_f_v - 2#64).toNat + 2 := by
    rw [hpf_back, m7_bv64_sub_toNat hpf_ge2, h2_64]; omega
  have hpi_f' : PropLitInv c F0 F_cur s_pi_p sem_f not_lit.toNat off_f_v.toNat
      q_f_v.toNat ((p_f_v - 2#64).toNat + 2) end_f_v.toNat := by
    rw [hoff_fv_n, hqf_n, hendf_n, hpv_sub2, hpf_n]; exact hpi_f
  have hq_le_pf : q_f_v.toNat ≤ (p_f_v - 2#64).toNat := by
    rw [m7_bv64_sub_toNat hpf_ge2, h2_64, hqf_n, hpf_n]; omega
  have hsub_q : q_f_v - off_f_v = q_p - off_o := by
    dsimp only [q_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hsub_p : (p_f_v - 2#64) + 1#64 + 1#64 - off_f_v = p_p - off_o := by
    rw [hpf_back]; dsimp only [p_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hsub_e : end_f_v - off_f_v = end_o - off_o := by
    dsimp only [end_f_v]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hoth_mask : (ovf_oth_p &&& 0x7FFFFFFF#32) = ovf_oth_p := by
    have := hlen4.core_ok.cur_vars_le; exact m7_bv32_mask7f_eq (by omega)
  have hcr_ref_f : ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_f.core :=
    hperm_f.2.1 ▸ (hpi_p.perm.2.1 ▸ hcr_ref)
  have hcsz_fp : fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat =
      fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat :=
    (hperm_f.2.2 ovf_cr_p.toNat (hpi_p.perm.2.1 ▸ hcr_ref)).1.trans
      (hpi_p.perm.2.2 ovf_cr_p.toNat (hpi_p.perm.2.1 ▸ hcr_ref)).1.symm
  have hcr_fit_f : ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat ≤
      sem_f.core.arena_len := by rw [halen_f, hcsz_fp]; exact hcr_fit
  have hri_lt_f : ovf_ri_p.toNat < fullArenaClauseSizeCore sem_f.core ovf_cr_p.toNat := by
    rw [hcsz_fp]; exact hri_lt
  obtain ⟨l0', l1', hwt_l, hoth_xor, har3, har4⟩ := hwt_p
  have har3_f : sem_f.core.arena[ovf_cr_p.toNat + 3]? = some l0' := by rw [har_f]; exact har3
  have har4_f : sem_f.core.arena[ovf_cr_p.toNat + 4]? = some l1' := by rw [har_f]; exact har4
  have har_ri_f : sem_f.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p := by
    rw [har_f]; exact har_ri
  have hoff4_lt_wv : 2 * not_lit.toNat < st4.core.wvec.length := by
    rw [hlen4.core_ok.wvec_len]; have := hlen4.core_ok.cur_vars_le; omega
  have hoff4_lt_m : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
      (fastPropMem s_disk st4).core.wvec.length := by
    rw [fastPropMem_wvec, hnl64_idx]; exact hoff4_lt_wv
  have h2n_lt64 : 2 * not_lit.toNat < 2 ^ 64 := by omega
  have hoff4_mod : 2 * not_lit.toNat % 2 ^ 64 = 2 * not_lit.toNat := Nat.mod_eq_of_lt h2n_lt64
  have hmem_wvec_get : ∀ {i : Nat} (hi : i = 2 * not_lit.toNat)
      (pf : i < (fastPropMem s_disk st4).core.wvec.length),
      ((fastPropMem s_disk st4).core.wvec[i]'pf).setWidth 64 =
      (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 := fun {i} hi pf => by
    have hg : (fastPropMem s_disk st4).core.wvec[i]? = st4.core.wvec[2 * not_lit.toNat]? := by
      rw [fastPropMem_wvec, hi]
    rw [List.getElem?_eq_getElem pf, List.getElem?_eq_getElem hoff4_lt_wv, Option.some.injEq] at hg
    exact congrArg (BitVec.setWidth 64) hg
  have hmem_len4 : (fastPropMem s_disk st4).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hlen4
      (by rw [hsd_cv, ← (hpi_p.ag.get FullCoreState.cur_vars), ← hcv4_p])
      (by rw [hag4.get FullCoreState.propagated, ← hsd_pr]; exact hsd_len.core_ok.propagated_le) rfl
  unfold s13OvfTailExpr
  s13_hsteps_nogrp
  refine wp_join_group (fun ((off_n, p_n, q_n, end_n, ()) :
      Tup Val [i64, i64, i64, i64]) mj =>
      mj = m4 ∧ off_n = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 ∧
      q_n = off_n + (q_p - off_o) ∧ p_n = off_n + (p_p - off_o) ∧
      end_n = off_n + (end_o - off_o)) ?_ ?_
  · rintro _ ⟨off_n, p_n, q_n, end_n, ⟨⟩⟩ mj ⟨rfl, hoff_n_def, hqn_d, hpn_d, hen_d⟩
    have hoff_n_eq : off_n = BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
      rw [hoff_n_def, List.getElem?_eq_getElem hoff4_lt_wv, Option.getD_some]
    have hqn_d' : q_n = off_n + (q_f_v - off_f_v) := by rw [hqn_d, hsub_q]
    have hpn_d' : p_n = off_n + ((p_f_v - 2#64) + 1#64 + 1#64 - off_f_v) := by rw [hpn_d, hsub_p]
    have hen_d' : end_n = off_n + (end_f_v - off_f_v) := by rw [hen_d, hsub_e]
    clear hoff_n_def hqn_d hpn_d hen_d
    subst hqn_d' hen_d' hpn_d' hoff_n_eq
    s13_hsplit
    · have hpok_t : pk = true := hc
      have hok := s13_ovf_ok_step hpi_f' hlen4 hcv4 hnot_f hlay4 hperm24 hnw4
        hag4 htr4 hrsns4 hsc4 hnot_f4 har4_eq hcr_fit_f hal4 hwt_l hoth_xor har3_f har4_f hri2
        hri_lt_f har_ri_f (hcv_f.symm ▸ hovf_lt) hovf_ne hcr_lt hcr_ref_f
        hpf_back_nat hq_le_pf hoth_pr (hpok_t_pr hpok_t)
      have hcr_u64 : ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat <
          2 ^ 64 := by
        have := hpi_p.len.core_ok.arena_len_le
        exact Nat.lt_of_le_of_lt (Nat.le_trans hcr_fit this) (Nat.lt_trans har (by decide))
      have har_m4 : (fastPropMem s_disk st4).core.arena.length = sem_p.core.arena.length := by
        rw [fastPropMem_arena, har4_eq, har_f]
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
      have har4_pf : st4.core.arena = sem_p.core.arena := har4_eq.trans har_f
      s13_hsteps
      let sem_n : FullState :=
        { st4 with core := { st4.core with
          arena := ((st4.core.arena.set (ovf_cr_p.toNat + 3) ovf_oth_p).set
            (ovf_cr_p.toNat + 4) ovf_rw_p).set (ovf_cr_p.toNat + 3 + ovf_ri_p.toNat) not_lit } }
      have hdel_sn : sem_n.scratch.delayed = sem_p.scratch.delayed := hdel4
      have hoff_n_u32 : (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32)).toNat <
          2 ^ 32 := by rw [bv_c0_zext32_64]; exact BitVec.isLt _
      have hdiff_o : (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
            (end_f_v - off_f_v)).toNat -
          (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
            ((p_f_v - 2#64) + 1#64 + 1#64 - off_f_v)).toNat = end_o.toNat - p_p.toNat := by
        rw [hsub_e, hsub_p, BitVec.toNat_add, BitVec.toNat_add,
          m7_bv64_sub_toNat (Nat.le_trans (Nat.le_trans hq_ge_o hq_le_o) hp_le_o),
          m7_bv64_sub_toNat (Nat.le_trans hq_ge_o hq_le_o),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      refine hJs0 _ m ⟨sem_n, by simpa only [sem_n, s_pi_p, hdel4, har4_pf] using hok,
        fun h0 => hdel_sn.trans (hd0_p h0), hte_p.trans hte4.symm, hun_p.trans hun4.symm,
        huf_p.trans huf4.symm, hoom4.trans hoom_p, s13ConflEq_trans hct4 hct_p, rfl,
        (by cases isBeyond <;> rfl), rfl, hdiff_o,
        fun _ => ⟨hoom4.trans hoom_p, s13ConflEq_trans hct4 hct_p⟩,
        by simpa only [sem_n, fastPropMem_arena, fastPropMem_with_arena,
          h3_idx, h31_idx, hri_idx] using hm⟩
    · have hpok_f : pk = false := hc
      let wv_n0 := (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64
      have hnot4_f : not_lit.toNat < 2 * sem_f.core.cur_vars := hnot_f
      obtain ⟨_, _, hp4_n, _, hq4_le_p4, _, hpi4⟩ := s13_ovf_pi4 (other := ovf_oth_p)
        (pok := false) hpi_f' hlen4
        hcv4 hnot4_f hlay4 hperm24 hnw4 hag4 htr4 hrsns4 hsc4 hnot_f4
        (hcv_f.symm ▸ hovf_lt) hovf_ne hcr_lt hcr_ref_f hpf_back_nat hq_le_pf hoth_pr
        (fun h => by cases h) (fun _ => hpok_f_pr hpok_f)
      let p4_v := wv_n0 + ((p_f_v - 2#64) + 1#64 + 1#64 - off_f_v)
      have hp4_ge2 : (2#64 : BitVec 64).toNat ≤ p4_v.toNat := by
        have := hpi_f'.sw.q_ge; have := hpi_f'.sw.q_le_p
        change 2 ≤ p4_v.toNat; dsimp only [p4_v]; rw [hp4_n]; omega
      have hp4_back : (p4_v - 2#64) + 1#64 + 1#64 = p4_v := by
        apply BitVec.eq_of_toNat_eq
        have h1 : (p4_v - 2#64).toNat + 1 < 2 ^ 64 := by
          rw [m7_bv64_sub_toNat hp4_ge2, h2_64]; omega
        rw [BitVec.toNat_add, BitVec.toNat_add, m7_bv64_sub_toNat hp4_ge2, h2_64, h1_64,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have hp4_back_nat : ((p4_v - 2#64) + 1#64 + 1#64).toNat = (p4_v - 2#64).toNat + 2 := by
        rw [hp4_back, m7_bv64_sub_toNat hp4_ge2, h2_64]; omega
      have hp4_sub2 : (p4_v - 2#64).toNat + 2 = p4_v.toNat := by
        rw [m7_bv64_sub_toNat hp4_ge2, h2_64]; omega
      have hq4_le_sub : (wv_n0 + (q_f_v - off_f_v)).toNat ≤ (p4_v - 2#64).toNat := by
        rw [m7_bv64_sub_toNat hp4_ge2, h2_64]; exact Nat.le_sub_of_add_le hq4_le_p4
      have hpi4' : PropLitInv c F0 F_cur s_pi_p st4 not_lit.toNat wv_n0.toNat
          (wv_n0 + (q_f_v - off_f_v)).toNat ((p4_v - 2#64).toNat + 2)
          (wv_n0 + (end_f_v - off_f_v)).toNat := by
        simpa only [hp4_sub2] using hpi4
      have hfail := m7_ovf_fail_step hpi4' hlen4 rfl hnot4 hlay4
        (fullArenaPermEq_refl st4.core) hnw4 (hpi4'.ag) (hpi4'.tr) (hpi4'.sc_eq) hnot_f4
        (hcv4_p.symm ▸ hovf_lt) hovf_ne hcr_lt (hperm24.2.1 ▸ hcr_ref_f)
        hp4_back_nat hq4_le_sub hoth_mask
        (fun l hl hne => ⟨rfl, fun _ _ => rfl⟩) ⟨rfl, fun _ _ => rfl⟩
      have hadd_sub (a b : BitVec 64) : a + b - a = b := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel]
      rw [hp4_back] at hfail
      dsimp only [p4_v, wv_n0] at hfail
      rw [hadd_sub] at hfail
      have hq_wlen : (wv_n0 + (q_f_v - off_f_v)).toNat <
          (fastPropMem s_disk st4).core.wstk.length := by rw [fastPropMem_wstk]; exact hfail.1
      have hq1_wlen : (wv_n0 + (q_f_v - off_f_v) + 1#64).toNat <
          (fastPropMem s_disk st4).core.wstk.length := by rw [fastPropMem_wstk]; exact hfail.2.1
      refine fc_let_mul rfl rfl ?_; refine fc_let_add rfl rfl ?_
      refine wp_store_sep (c0_store_full_wstk ovf_oth_p
        (by dsimp only [Arg.val]; exact hq_wlen) hm4) ?_
      intro m5a hm5a; clear hm4; dsimp only [Arg.val] at hm5a
      rw [fastPropMem_wstk, fastPropMem_with_wstk] at hm5a
      refine fc_let_add rfl rfl ?_; refine fc_let_mul rfl rfl ?_; refine fc_let_add rfl rfl ?_
      let st4a : FullState := { st4 with core := { st4.core with
        wstk := st4.core.wstk.set (wv_n0 + (q_f_v - off_f_v)).toNat ovf_oth_p } }
      have hq1_wlen_a : (wv_n0 + (q_f_v - off_f_v) + 1#64).toNat <
          (fastPropMem s_disk st4a).core.wstk.length := by
        rw [fastPropMem_wstk, List.length_set, ← fastPropMem_wstk]; exact hq1_wlen
      refine wp_store_sep (c0_store_full_wstk ovf_cr_p
        (by dsimp only [Arg.val]; exact hq1_wlen_a) hm5a) ?_
      intro m_fin hm_fin; clear hm5a; dsimp only [Arg.val] at hm_fin
      refine fc_let_add rfl rfl ?_; s13_hsteps
      let st5 : FullState := { st4 with core := { st4.core with
        wstk := (st4.core.wstk.set (wv_n0 + (q_f_v - off_f_v)).toNat ovf_oth_p).set
          ((wv_n0 + (q_f_v - off_f_v)).toNat + 1) ovf_cr_p } }
      have hdel5 : st5.scratch.delayed = sem_p.scratch.delayed := hdel4
      refine hBo _ _ ⟨st5,
        by
          dsimp only [st5, s_pi_p, wv_n0] at hfail ⊢
          rw [hdel4]
          simp only [hsub_q, hadd_sub] at hfail ⊢
          rw [show (2#64 : BitVec 64) = 2 from by decide] at hfail
          exact hfail.2.2.2.2.2.2.2,
        rfl, fun h0 => hdel5.trans (hd0_p h0), hte_p.trans hte4.symm, hun_p.trans hun4.symm,
        huf_p.trans huf4.symm, rfl, s13ConflEq_trans hct4 hct_p, ?_⟩
      have h1_idx : (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
          (q_f_v - off_f_v) + 1).toNat = (wv_n0 + (q_f_v - off_f_v)).toNat + 1 := hfail.2.2.1
      rw [fastPropMem_wstk, fastPropMem_with_wstk, h1_idx] at hm_fin; exact hm_fin
  · intro Jn hJn; s13_hsplit
    · s13_hsteps; exact hJn _ m4 ⟨rfl, hmem_wvec_get hnl64_idx hoff4_lt_m, rfl, rfl, rfl⟩
    · s13_hsteps
      have hoff_eq : off_o = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 := by
        simpa only [hoff4_mod, List.getElem?_eq_getElem hoff4_lt_wv, Option.getD_some] using hc.symm
      have had_sub : ∀ {x : BitVec 64}, off_o.toNat ≤ x.toNat → x.toNat < 2 ^ 64 →
          x = off_o + (x - off_o) := fun {x} hle hlt => by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, m7_bv64_sub_toNat hle, Nat.mod_eq_of_lt (by omega)]; omega
      have hend_lt : end_o.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt
        (Nat.le_trans (hpi_p.end_lt_wcap hnot_lt).1 (hpi_p.end_lt_wcap hnot_lt).2)
        (Nat.lt_trans hwc (by decide))
      exact hJn _ m4 ⟨rfl, hoff_eq, had_sub hq_ge_o (by omega),
        had_sub (Nat.le_trans hq_ge_o hq_le_o) (by omega),
        had_sub (Nat.le_trans hq_ge_o (Nat.le_trans hq_le_o hp_le_o)) hend_lt⟩

/-- Pack an `11`-tuple `(te..di, brk, ovf)` into `s13LoSig isBeyond` (dropping `brk` if `true`). -/
abbrev s13LoTup (isBeyond : Bool)
    (xs : Tup Val [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]) :
    Tup Val (s13LoSig isBeyond) :=
  match isBeyond with
  | true => (xs.1, xs.2.1, xs.2.2.1, xs.2.2.2.1, xs.2.2.2.2.1, xs.2.2.2.2.2.1,
      xs.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.1,
      xs.2.2.2.2.2.2.2.2.2.2.1, ())
  | false => xs

/-- Pack a `13`-tuple `(te..di, brk, ovf, rw, oth, cr, ri)` into `s13OvfSig isBeyond`. -/
abbrev s13OvfTup (isBeyond : Bool)
    (xs : Tup Val [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]) :
    Tup Val (s13OvfSig isBeyond) :=
  match isBeyond with
  | true => (xs.1, xs.2.1, xs.2.2.1, xs.2.2.2.1, xs.2.2.2.2.1, xs.2.2.2.2.2.1,
      xs.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.2.1,
      xs.2.2.2.2.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.2.2.2.1,
      xs.2.2.2.2.2.2.2.2.2.2.2.2.1, ())
  | false => xs

theorem s13_post_lp_ovf_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_disk s_base sem sem_o sem_p : FullState}
    {not_lit ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32}
    {ign_v nl64 off_o p_o end_o p_p q_p te_p un_p uf_p tk_p di_p brk_p ovf_ri_p : BitVec 64}
    {ovf_p : Bool} {dlen_p : Nat}
    {Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    {Lo : Cont (s13LoSig isBeyond)} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {mbp : Mem 64}
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" fidPropFlushDelSpec)
    (hBo : ∀ xs mb,
      (∃ (sem_b : FullState) (dlen_b : Nat),
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
          sem_b not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
          xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
        xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
        xs.1.toNat = sem_b.core.trail_end ∧ xs.2.1 = sem_b.core.unassigned ∧
        xs.2.2.1 = sem_b.core.unflushed ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_b.core.oom = 0#64 ∧
          (isBeyond = false → sem_b.core.confl_type = s.core.confl_type) ∧
          (xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1)) ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
          PropLitConfl F_cur ign_v sem_b.core ∧ sem_b.core.oom = 0#64) ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64 ∨
          xs.2.2.2.2.2.2.2.2.2.1 = 2#64) ∧
        S13ConflEq sem_o.core sem_b.core ∧ (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) →
      Bo xs mb)
    (hLo : ∀ rem xs m,
      rem < (end_o.toNat - p_o.toNat) + 1 →
      (∃ (sem_o' : FullState) (dlen_o' : Nat),
        rem = (xs.2.2.2.2.2.2.2.1.toNat - xs.2.2.2.2.2.1.toNat) +
          (if xs.2.2.2.2.2.2.2.2.2.2.1 then 1 else 0) ∧
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_o'.scratch.delayed } }
          sem_o' not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
          xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
        xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_o' ∧ dlen_o' ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_o'.scratch.delayed dlen_o' not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_o'.scratch.delayed = s.scratch.delayed) ∧
        xs.1.toNat = sem_o'.core.trail_end ∧ xs.2.1 = sem_o'.core.unassigned ∧
        xs.2.2.1 = sem_o'.core.unflushed ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∧
          sem_o'.core.oom = 0#64 ∧ S13ConflEq sem_o.core sem_o'.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = false →
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_o'.core.oom = 0#64 ∧
            S13ConflEq sem_o.core sem_o'.core ∧ xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 →
            isBeyond = false ∧ PropLitConfl F_cur ign_v sem_o'.core ∧ sem_o'.core.oom = 0#64) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64)) ∧
        (FullMem c (fastPropMem s_disk sem_o') ⋆ R) m) →
      Lo (s13LoTup isBeyond xs) m)
    (har : c.arena_cap < 2 * dimacsBound) (hwc : c.wcap < 2 * dimacsBound)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = s_base.core.cur_vars)
    (hsd_pr : s_disk.core.propagated = s_base.core.propagated)
    (hpo_le_pp : p_o.toNat ≤ p_p.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem_p.core.cur_vars)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat)) (hnl64_idx : nl64.toNat = 2 * not_lit.toNat)
    (hoff_o : off_o.toNat = fullWatchOffCore sem_p.core not_lit.toNat)
    (hpi_p : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
      sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat)
    (hdi_p : di_p.toNat = 3 * dlen_p) (hdl_p : dlen_p ≤ c.delayed_cap)
    (hdok_p : DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat)
    (hd0_p : c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed)
    (hte_p : te_p.toNat = sem_p.core.trail_end) (hun_p : un_p = sem_p.core.unassigned)
    (huf_p : uf_p = sem_p.core.unflushed) (hoom_p : sem_p.core.oom = 0#64)
    (hnoov : ovf_p = false →
      (brk_p = 0#64 → p_p = end_o ∧ S13ConflEq sem_o.core sem_p.core) ∧
      (brk_p = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_p.core) ∧
      (brk_p = 0#64 ∨ brk_p = 1#64))
    (hov_yes : ovf_p = true → brk_p = 0#64 ∧ S13ConflEq sem_o.core sem_p.core ∧
      2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
      end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
      ovf_cr_p.toNat < 0x80000000 ∧ ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
      ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
        sem_p.core.arena_len ∧
      ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧ ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri_p.toNat ∧
      ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
      (∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ ovf_oth_p = l0' ^^^ l1' ^^^ not_lit ∧
        sem_p.core.arena[ovf_cr_p.toNat + 3]? = some l0' ∧
        sem_p.core.arena[ovf_cr_p.toNat + 4]? = some l1') ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hmbp : (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) :
    wp Γ Q X (s13PostLpOvfExpr isBeyond c nl64 not_lit off_o end_o Bo Lo
      te_p un_p uf_p tk_p p_p q_p di_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p) mbp := by
  have _ := (ovf_p, p_o, sem.core); have _ := hoff_o
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  rw [hnl64]; unfold s13PostLpOvfExpr
  refine wp_unroll_group fun _Js0 _hJs0 => ?_
  s13_hsplit
  · have hovf_true : ovf_p = true := hc
    obtain ⟨rfl, hct_p, hp_off2, hq_pp2, hdec_o, hcr_lt, hcr_ref, hcr_fit,
      hoth_lt, hovf_lt, hovf_ne, hri2, hri_lt, hwt_p, har_ri⟩ := hov_yes hovf_true
    subst hovf_true
    have hnot_c : not_lit.toNat < 2 * c.max_vars := by have := hpi_p.len.core_ok.cur_vars_le; omega
    let s_pi_p : FullState :=
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
    have hsd_cv_b : s_disk.core.cur_vars = s_base.core.cur_vars := hsd_cv
    have hsd_pr_b : s_disk.core.propagated = s_base.core.propagated := hsd_pr
    let P_jf : BitVec 64 × Bool → Mem 64 → Prop := fun (di_f, fok) mf =>
      ∃ sem_f : FullState,
        di_f = 0#64 ∧ sem_f.LengthsOk c ∧ WatchStackLayout sem_f.core ∧
        FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem_f.core) ∧
        AgreesExcept propLitCoreMask s_base.core sem_f.core ∧
        FullTrailExt s_base.core sem_f.core ∧ FullTrailRsnsPres s_base.core sem_f.core ∧
        FullArenaPermEq s_base.core sem_f.core ∧
        sem_f.core.cur_vars = sem_p.core.cur_vars ∧ sem_f.core.vals = sem_p.core.vals ∧
        sem_f.core.arena = sem_p.core.arena ∧ sem_f.core.arena_len = sem_p.core.arena_len ∧
        sem_f.core.trail_end = sem_p.core.trail_end ∧
        sem_f.core.unassigned = sem_p.core.unassigned ∧
        sem_f.core.unflushed = sem_p.core.unflushed ∧ sem_f.core.oom = sem_p.core.oom ∧
        S13ConflEq sem_p.core sem_f.core ∧
        sem_f.scratch = { s_pi_p.scratch with
          search_ticks := sem_f.scratch.search_ticks, wsort := sem_f.scratch.wsort,
          phases := sem_f.scratch.phases } ∧
        sem_f.scratch.delayed = sem_p.scratch.delayed ∧
        (let off_f := fullWatchOffCore sem_f.core not_lit.toNat
         SplitWatchesInv F_cur sem_f.core not_lit.toNat off_f
           (off_f + (q_p.toNat - off_o.toNat)) (off_f + (p_p.toNat - off_o.toNat))
           (off_f + (end_o.toNat - off_o.toNat))) ∧
        (FullMem c (fastPropMem s_disk sem_f) ⋆ R) mf
    refine wp_join_group (fun (di_f, fok, ()) mf => P_jf (di_f, fok) mf) ?_ ?_
    · rintro _ ⟨di_f, fok, ⟨⟩⟩ mf
        ⟨sem_f, rfl, hlen_f, hlay_f, hnw_f, hag_f, htr_f, hrsns_f, hperm_f, hcv_f, hvals_f, har_f,
          halen_f, hte_f, hun_f, huf_f, hoom_f, hct_f, hsc_f, hdel_f, hsw_f, hmf⟩
      let P_jp : Bool → Mem 64 → Prop := fun pk m4 =>
        ∃ st4 : FullState,
          st4.LengthsOk c ∧ WatchStackLayout st4.core ∧
          FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) ∧
          AgreesExcept propLitCoreMask s_base.core st4.core ∧
          FullTrailExt s_base.core st4.core ∧ FullTrailRsnsPres s_base.core st4.core ∧
          FullArenaPermEq sem_f.core st4.core ∧
          st4.core.cur_vars = sem_f.core.cur_vars ∧ st4.core.vals = sem_f.core.vals ∧
          st4.core.arena = sem_f.core.arena ∧ st4.core.arena_len = sem_f.core.arena_len ∧
          st4.core.trail_end = sem_p.core.trail_end ∧ st4.core.unassigned = sem_p.core.unassigned ∧
          st4.core.unflushed = sem_p.core.unflushed ∧ st4.core.oom = sem_p.core.oom ∧
          S13ConflEq sem_p.core st4.core ∧
          st4.scratch = { s_pi_p.scratch with
            search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
            phases := st4.scratch.phases } ∧
          st4.scratch.delayed = sem_p.scratch.delayed ∧
          (∀ l < 2 * sem_f.core.cur_vars, l ≠ ovf_rw_p.toNat →
            fullWatchSizeCore st4.core l = fullWatchSizeCore sem_f.core l ∧
            ∀ k < fullWatchSizeCore sem_f.core l,
              st4.core.wstk[fullWatchOffCore st4.core l + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core l + k]?) ∧
          (pk = true →
            fullWatchSizeCore st4.core ovf_rw_p.toNat =
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 2 ∧
            (∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
              st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?) ∧
            st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat]? = some (ovf_oth_p &&& 0x7FFFFFFF#32) ∧
            st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat +
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat + 1]? = some ovf_cr_p) ∧
          (pk = false →
            fullWatchSizeCore st4.core ovf_rw_p.toNat =
              fullWatchSizeCore sem_f.core ovf_rw_p.toNat ∧
            ∀ k < fullWatchSizeCore sem_f.core ovf_rw_p.toNat,
              st4.core.wstk[fullWatchOffCore st4.core ovf_rw_p.toNat + k]? =
                sem_f.core.wstk[fullWatchOffCore sem_f.core ovf_rw_p.toNat + k]?) ∧
          (FullMem c (fastPropMem s_disk st4) ⋆ R) m4
      refine wp_join_group (fun (pk, ()) m4 => P_jp pk m4) ?_ ?_
      · rintro _ ⟨pk, ⟨⟩⟩ m4
          ⟨st4, hlen4, hlay4, hnw4, hag4, htr4, hrsns4, hperm24, hcv4, hvals4, har4_eq, hal4,
            hte4, hun4, huf4, hoom4, hct4, hsc4, hdel4, hoth_pr, hpok_t_pr, hpok_f_pr, hmo'⟩
        change wp Γ Q X (s13OvfTailExpr isBeyond c (not_lit.setWidth 64 <<< (1 : Nat)) not_lit
          off_o end_o Bo _Js0 te_p un_p uf_p tk_p p_p q_p 0#64 0#64 true pk ovf_rw_p ovf_oth_p
          ovf_cr_p ovf_ri_p) m4
        exact s13_ovf_tail_wp (isBeyond := isBeyond) har hwc hnot_lt (hpi_p.sw.off_eq.symm)
          hsd_len hsd_cv hsd_pr hd0_p hpi_p hp_off2 hq_pp2 hcr_lt hcr_ref hcr_fit hoth_lt hovf_lt
          hovf_ne hri2 hri_lt hwt_p har_ri (by rw [← hnl64]; exact hnl64_idx) hct_p hoom_p rfl
          hlen_f hlay_f hnw_f hag_f htr_f hrsns_f hperm_f hcv_f hvals_f har_f halen_f hsc_f hsw_f
          hlen4 hlay4 hnw4 hag4 htr4 hrsns4 hperm24 hcv4 hvals4 har4_eq hal4 hte4 hun4 huf4 hoom4
          hct4 hsc4 hdel4 hoth_pr hpok_t_pr hpok_f_pr hte_p hun_p huf_p hmo'
          (fun x mj ⟨sem_n, hpi_n, hd0_n, hte_n, hun_n, huf_n, hoom_n, hct_n, hdi0, hbrk0, hdi0n,
              hdiff, _, hm_n⟩ => by
            cases isBeyond <;>
            · refine _hJs0 x mj ?_; (try dsimp only [Blocks.get]); s13_hsteps
              exact hLo (end_o.toNat - p_p.toNat + 1)
                (te_p, un_p, uf_p, tk_p, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
                  x.2.2.2.2.2.1, true, ()) mj
                (Nat.add_lt_add_right hdec_o 1)
                ⟨sem_n, 0, by simp only [↓reduceIte, hdiff], hpi_n, hdi0n, Nat.zero_le _,
                  fun _ hj => absurd hj (Nat.not_lt_zero _), hd0_n, hte_n, hun_n, huf_n,
                  fun _ => ⟨hbrk0, hoom_n, hct_n⟩, fun h => Bool.noConfusion h, hm_n⟩)
          (fun x mb ⟨sem_b, hpi_b, hdi0, hd0_b, hte_b, hun_b, huf_b, hbrk2, hcf_b, hmb⟩ =>
            hBo x mb ⟨sem_b, 0, hpi_b, by rw [hdi0]; rfl, Nat.zero_le _,
              fun _ hj => absurd hj (Nat.not_lt_zero _), hd0_b, hte_b, hun_b, huf_b,
              fun h => absurd h (by rw [hbrk2]; decide), fun h => absurd h (by rw [hbrk2]; decide),
              Or.inr (Or.inr hbrk2), hcf_b, hmb⟩) rfl
      · intro Jp hJp
        have hnot_f : not_lit.toNat < 2 * sem_f.core.cur_vars := hcv_f.symm ▸ hnot_lt
        s13_hsplit
        · have hlay_mf := fastPropMem_watchLayout (s0 := s_disk) hlay_f rfl
          have hlen_mf := fastPropMem_lengthsOk hsd_len hlen_f
            (by rw [hsd_cv_b, hcv_f, (hpi_p.ag.get FullCoreState.cur_vars)])
            (by rw [hag_f.get FullCoreState.propagated, ← hsd_pr_b]
                exact hsd_len.core_ok.propagated_le) rfl
          have hcv_fl : sem_p.core.cur_vars ≤ c.max_vars := hcv_f ▸ hlen_f.core_ok.cur_vars_le
          c0_call hOvf
          refine ⟨c, fastPropMem s_disk sem_f, R, rfl, hlen_mf, hlay_mf,
            fun h => absurd h (by decide),
            fun _ => ⟨fun h => absurd h (fun h' => by
                have h_nat := congrArg BitVec.toNat h'
                rw [show (4294967295#32 : BitVec 32).toNat = 4294967295 from by decide] at h_nat
                have hcv_p := hpi_p.len.core_ok.cur_vars_le
                omega),
              fun h => by rw [h] at hcr_lt; revert hcr_lt; decide⟩,
            hmf, fun pok wv' ws' wl' wu' wsrt' mo' hlen' hlay' hoth_pr hnew_pr hfail_pr hmo' => ?_⟩
          let st4 : FullState :=
            { sem_f with
              core := { sem_f.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
              scratch := { sem_f.scratch with wsort := wsrt' } }
          have hlen4 : st4.LengthsOk c := by
            rw [fastPropMem_def] at hlen'
            exact ⟨{ hlen_f.core_ok with
                wvec_len := hlen'.core_ok.wvec_len, wstk_len_arr := hlen'.core_ok.wstk_len_arr,
                wlen_le := hlen'.core_ok.wlen_le },
              { hlen_f.scratch_ok with wsort_len := hlen'.scratch_ok.wsort_len }⟩
          have hlay4 : WatchStackLayout st4.core :=
            hlay'.with_wstk (fastPropMem_cur_vars s_disk sem_f).symm rfl rfl rfl
          exact hJp (pok, ()) mo' ⟨st4, hlen4, hlay4,
            fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw_f rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl,
            hag_f.update
              (fun k => { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }),
            fullTrailExt_congr htr_f rfl rfl rfl, fullTrailRsnsPres_congr hrsns_f rfl,
            ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩,
            rfl, rfl, rfl, rfl, hte_f, hun_f, huf_f, hoom_f, hct_f, by dsimp only [st4]; rw [hsc_f],
            hdel_f,
            fun l hl hne => by
              have h := hoth_pr l (by simpa only [fastPropMem_cur_vars] using hl) hne
              simpa only [st4, fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                fastPropMem_wvec, fastPropMem_wstk] using h,
            fun ht => by
              have ⟨h1, h2, h3, h4⟩ := (hnew_pr ht).2.2
              refine ⟨?_, ?_, ?_, ?_⟩
              · simpa only [st4, fullWatchSize, fullWatchSizeCore, fastPropMem_wvec,
                  show (2#32 : BitVec 32).toNat = 2 from rfl] using h1
              · simpa only [st4, fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                  fastPropMem_wvec, fastPropMem_wstk] using h2
              · rw [m7_bv32_mask7f_eq (by omega : ovf_oth_p.toNat < 2 ^ 31)]
                simpa only [st4, fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                  fastPropMem_wvec, fastPropMem_wstk] using h3
              · simpa only [st4, fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                  fastPropMem_wvec, fastPropMem_wstk] using (h4 rfl),
            fun hf => by
              have h := (hfail_pr hf).1 (by simpa only [fastPropMem_cur_vars, hcv_f] using hovf_lt)
              simpa only [st4, fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                fastPropMem_wvec, fastPropMem_wstk] using h,
            by simpa only [st4, fastPropMem_def] using hmo'⟩
        · dsimp only; s13_hsteps
          exact hJp (false, ()) mf ⟨sem_f, hlen_f, hlay_f, hnw_f, hag_f, htr_f, hrsns_f,
            fullArenaPermEq_refl _, rfl, rfl, rfl, rfl, hte_f, hun_f, huf_f, hoom_f, hct_f, hsc_f,
            hdel_f, fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩, fun h => absurd h (by decide),
            fun _ => ⟨rfl, fun _ _ => rfl⟩, hmf⟩
    · intro Jf hJf; have hlay_p : WatchStackLayout sem_p.core := hpi_p.sw.layout
      s13_hsplit
      · have hdi_pos : 0 < di_p.toNat := hc
        have hlay_mp := fastPropMem_watchLayout (s0 := s_disk) hlay_p rfl
        have hlen_mp := fastPropMem_lengthsOk hsd_len hpi_p.len
          (by rw [hsd_cv_b, (hpi_p.ag.get FullCoreState.cur_vars)])
          (by rw [hpi_p.ag.get FullCoreState.propagated, ← hsd_pr_b]
              exact hsd_len.core_ok.propagated_le) rfl
        have hdok_mp : DelayedWatchesOk (fastPropMem s_disk sem_p).core
            (fastPropMem s_disk sem_p).scratch.delayed dlen_p not_lit.toNat := by
          rw [fastPropMem_delayed]
          exact delayedWatchesOk_congr hdok_p
            (by rw [fastPropMem_cur_vars]; exact hpi_p.ag.get FullCoreState.cur_vars)
            (fun r hr => by
              have hr' : r ∈ fullArenaClauseRefsCore sem_p.core := hpi_p.perm.2.1.symm ▸ hr
              simpa only [fullArenaClauseRefsCore, fastPropMem_arena, fastPropMem_arena_len]
                using hr')
        c0_call hFlush
        refine ⟨c, F_cur, fastPropMem s_disk sem_p, R, dlen_p, not_lit.toNat, rfl, hlen_mp,
          hlay_mp, hdi_p, hdl_p, hdok_mp, hmbp,
          fun fok wv' ws' wl' wu' wsrt' mf1 hlen' hlay' _hwat' hsw' hmf1 => ?_⟩
        let sem_f : FullState :=
          { sem_p with
            core := { sem_p.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
            scratch := { sem_p.scratch with wsort := wsrt' } }
        have hlen_f : sem_f.LengthsOk c := by
          rw [fastPropMem_def] at hlen'
          exact ⟨{ hpi_p.len.core_ok with
              wvec_len := hlen'.core_ok.wvec_len, wstk_len_arr := hlen'.core_ok.wstk_len_arr,
              wlen_le := hlen'.core_ok.wlen_le },
            { hpi_p.len.scratch_ok with wsort_len := hlen'.scratch_ok.wsort_len }⟩
        have hlay_f : WatchStackLayout sem_f.core :=
          hlay'.with_wstk (fastPropMem_cur_vars s_disk sem_p).symm rfl rfl rfl
        have hsw_mp : SplitWatchesInv F_cur (fastPropMem s_disk sem_p).core not_lit.toNat
            off_o.toNat q_p.toNat p_p.toNat end_o.toNat :=
          SplitWatchesInv.with_nonwatch hpi_p.sw (fastPropMem_cur_vars _ _) (fastPropMem_wvec _ _)
            (fastPropMem_wstk _ _) (fastPropMem_wlen _ _)
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_arena, fastPropMem_arena_len]
                exact fun _ hr => hr)
        have hsw_f_raw := hsw' (by rw [fastPropMem_cur_vars]; exact hnot_lt)
          off_o.toNat q_p.toNat p_p.toNat end_o.toNat hsw_mp
        have hsw_f : SplitWatchesInv F_cur sem_f.core not_lit.toNat
            (fullWatchOffCore sem_f.core not_lit.toNat)
            (fullWatchOffCore sem_f.core not_lit.toNat + (q_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (p_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_f.core not_lit.toNat + (end_o.toNat - off_o.toNat)) := by
          refine SplitWatchesInv.with_nonwatch hsw_f_raw
            (by dsimp only [sem_f]; exact (fastPropMem_cur_vars s_disk sem_p).symm) rfl rfl rfl ?_
          unfold fullArenaClauseRefsCore; rw [fastPropMem_arena, fastPropMem_arena_len]
          exact fun _ hr => hr
        exact hJf (0#64, fok, ()) mf1 ⟨sem_f, rfl, hlen_f, hlay_f,
          fullWitnessInv_nw_congr hlen_f.core_ok.cur_vars_le hpi_p.nw
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
          hpi_p.ag.update
            (fun k => { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }),
          fullTrailExt_congr hpi_p.tr rfl rfl rfl, fullTrailRsnsPres_congr hpi_p.rsns_pres rfl,
          hpi_p.perm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩,
          by dsimp only [sem_f]; rw [hpi_p.sc_eq], rfl, hsw_f,
          by simpa only [sem_f, fastPropMem_def] using hmf1⟩
      · have hdi0 : di_p = 0#64 := BitVec.eq_of_toNat_eq (by
          have hc' : ¬ (0 : BitVec 64).toNat < di_p.toNat := hc
          change ¬ 0 < di_p.toNat at hc'
          rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; omega)
        have hsw_p' : SplitWatchesInv F_cur sem_p.core not_lit.toNat
            (fullWatchOffCore sem_p.core not_lit.toNat)
            (fullWatchOffCore sem_p.core not_lit.toNat + (q_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_p.core not_lit.toNat + (p_p.toNat - off_o.toNat))
            (fullWatchOffCore sem_p.core not_lit.toNat + (end_o.toNat - off_o.toNat)) := by
          rw [hpi_p.sw.off_eq]
          have hq_ge := hpi_p.sw.q_ge; have hq_le := hpi_p.sw.q_le_p
          have hp_le := hpi_p.sw.p_le_end
          rw [Nat.add_sub_cancel' hq_ge, Nat.add_sub_cancel' (Nat.le_trans hq_ge hq_le),
            Nat.add_sub_cancel' (Nat.le_trans (Nat.le_trans hq_ge hq_le) hp_le)]
          exact hpi_p.sw
        s13_hsteps
        rw [hdi0]
        exact hJf (0#64, true, ()) mbp ⟨sem_p, rfl, hpi_p.len, hlay_p, hpi_p.nw, hpi_p.ag,
          fullTrailExt_congr hpi_p.tr rfl rfl rfl, fullTrailRsnsPres_congr hpi_p.rsns_pres rfl,
          hpi_p.perm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hpi_p.sc_eq,
          rfl, hsw_p', hmbp⟩
  · have hovf_false : ovf_p = false := hc
    subst hovf_false
    have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
    cases isBeyond <;>
    · s13_hsteps
      dsimp only [s13LoJump]
      s13_hsteps
      exact hLo (end_o.toNat - p_p.toNat)
        (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, di_p, brk_p, false, ()) mbp
        (by omega)
        ⟨sem_p, dlen_p, by simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero], hpi_p,
          hdi_p, hdl_p, hdok_p, hd0_p, hte_p, hun_p, huf_p, fun h => Bool.noConfusion h,
          fun _ => ⟨fun h0 => ⟨hoom_p, (hbrk0_fn h0).2, (hbrk0_fn h0).1⟩,
            fun h1 => let h := hbrk1_fn h1; ⟨h.1, h.2, hoom_p⟩, hbrk_disj⟩,
          hmbp⟩

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
