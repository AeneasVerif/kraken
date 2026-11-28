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
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfTail
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
# Kissat Canonical Outer `while (ovf)` Loop WP Proofs (`PropSearch.WpOvfLoop`)

Plain `public section` (`@[expose]` ONLY on concrete AST `Expr` builders, `0` `@[expose]` on
theorems/lemmas, `0` legacy imports, `<= 100` cols, every theorem `<= 350` lines):
1. `S13OuterInv`, `s13OuterInv_mk`, `s13OuterInv_elim`:
   outer `while (prop < tend && ...)` invariant.
2. `s13OvfLoopBody`, `s13OvfLoopExpr`: parameterized `while (ovf)` AST builders.
3. `s13_ovf_loop_body_wp`: inner `s13_lp_loop_wp` -> `s13_post_lp_ovf_wp` / `Bo` / `Lo` bridge.
-/

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

/-! ## 1. Shared Outer Invariant & `while (ovf)` AST Builders -/

/-- Step-13 outer propagation loop invariant (`S13OuterInv`), threading `ext1`,
`FullTrailRsnsPres`, `S13Scr`, and `red_refs` framing across `FullM6HdrMem`. -/
def S13OuterInv (isBeyond : Bool) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop) (rem : Nat)
    (prop_v tend_v fuel_v unass_v unfl_v _ticks_v : BitVec 64) (m : Mem 64) : Prop :=
  ∃ (ext1 : List (BitVec 64)) (sem : FullState) (te_mem : Nat),
    rem = sem.core.fuel.toNat ∧
    M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1) ∧
    sem.LengthsOk c ∧ FullWitnessInv c F0 F_cur sem.core ∧
    FullTrailExt s.core sem.core ∧ FullTrailRsnsPres s.core sem.core ∧
    FullArenaPermEq s.core sem.core ∧
    AgreesExcept fidCoreMask s.core sem.core ∧
    sem.core.propagated = prop_v.toNat ∧ sem.core.trail_end = tend_v.toNat ∧
    sem.core.fuel = fuel_v ∧ sem.core.unassigned = unass_v ∧ sem.core.unflushed = unfl_v ∧
    sem.core.oom = 0#64 ∧ (isBeyond = false → sem.core.confl_type = s.core.confl_type) ∧
    (isBeyond = true → S13ConflEq s.core sem.core) ∧
    sem.core.dense_mode = 0#64 ∧ sem.core.cur_vars = s.core.cur_vars ∧
    sem.core.cur_level = s.core.cur_level ∧ sem.core.probing = s.core.probing ∧
    sem.core.arena_len = s.core.arena_len ∧ sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
    s.core.propagated ≤ prop_v.toNat ∧ prop_v.toNat ≤ tend_v.toNat ∧
    te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem ∧ S13Scr s sem ∧
    (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
    (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mem } }
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆
      R) m

theorem s13OuterInv_mk {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {rem : Nat}
    {prop_v tend_v fuel_v unass_v unfl_v ticks_v : BitVec 64} {m : Mem 64}
    (h : ∃ (ext1 : List (BitVec 64)) (sem : FullState) (te_mem : Nat),
      rem = sem.core.fuel.toNat ∧
      M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1) ∧
      sem.LengthsOk c ∧ FullWitnessInv c F0 F_cur sem.core ∧
      FullTrailExt s.core sem.core ∧ FullTrailRsnsPres s.core sem.core ∧
      FullArenaPermEq s.core sem.core ∧
      AgreesExcept fidCoreMask s.core sem.core ∧
      sem.core.propagated = prop_v.toNat ∧ sem.core.trail_end = tend_v.toNat ∧
      sem.core.fuel = fuel_v ∧ sem.core.unassigned = unass_v ∧ sem.core.unflushed = unfl_v ∧
      sem.core.oom = 0#64 ∧ (isBeyond = false → sem.core.confl_type = s.core.confl_type) ∧
      (isBeyond = true → S13ConflEq s.core sem.core) ∧
      sem.core.dense_mode = 0#64 ∧ sem.core.cur_vars = s.core.cur_vars ∧
      sem.core.cur_level = s.core.cur_level ∧ sem.core.probing = s.core.probing ∧
      sem.core.arena_len = s.core.arena_len ∧ sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
      s.core.propagated ≤ prop_v.toNat ∧ prop_v.toNat ≤ tend_v.toNat ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem ∧ S13Scr s sem ∧
      (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mem } }
        { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } })
        ⋆ R) m) :
    S13OuterInv isBeyond c F0 F_cur ext0 s R rem prop_v tend_v fuel_v unass_v unfl_v ticks_v m :=
  h

theorem s13OuterInv_elim {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {rem : Nat}
    {prop_v tend_v fuel_v unass_v unfl_v ticks_v : BitVec 64} {m : Mem 64}
    (h : S13OuterInv isBeyond c F0 F_cur ext0 s R rem
      prop_v tend_v fuel_v unass_v unfl_v ticks_v m) :
    ∃ (ext1 : List (BitVec 64)) (sem : FullState) (te_mem : Nat),
      rem = sem.core.fuel.toNat ∧
      M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1) ∧
      sem.LengthsOk c ∧ FullWitnessInv c F0 F_cur sem.core ∧
      FullTrailExt s.core sem.core ∧ FullTrailRsnsPres s.core sem.core ∧
      FullArenaPermEq s.core sem.core ∧
      AgreesExcept fidCoreMask s.core sem.core ∧
      sem.core.propagated = prop_v.toNat ∧ sem.core.trail_end = tend_v.toNat ∧
      sem.core.fuel = fuel_v ∧ sem.core.unassigned = unass_v ∧ sem.core.unflushed = unfl_v ∧
      sem.core.oom = 0#64 ∧ (isBeyond = false → sem.core.confl_type = s.core.confl_type) ∧
      (isBeyond = true → S13ConflEq s.core sem.core) ∧
      sem.core.dense_mode = 0#64 ∧ sem.core.cur_vars = s.core.cur_vars ∧
      sem.core.cur_level = s.core.cur_level ∧ sem.core.probing = s.core.probing ∧
      sem.core.arena_len = s.core.arena_len ∧ sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
      s.core.propagated ≤ prop_v.toNat ∧ prop_v.toNat ≤ tend_v.toNat ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem ∧ S13Scr s sem ∧
      (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mem } }
        { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } })
        ⋆ R) m :=
  h

/-- Shared `while (ovf)` body parameterized over `isBeyond : Bool`. -/
@[expose] def s13OvfLoopBody (c : FullCfg) (isBeyond : Bool)
    (Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (Lo : Cont (s13LoSig isBeyond))
    (dlim : Val i64) (ignore_ref : Arg Val i64) (two_cv : Val i64)
    (cur_lvl32 not_lit nl_lvl : Val i32) (rec_ph bigbig : Val Ty.bool) (nl64 : Val i64)
    (te_o un_o uf_o tk_o off_o p_o q_o end_o di_o brk_o : Val i64) (ovf_o : Val Ty.bool) :
    Expr Val Cont [i64] :=
  Expr.jnz (Arg.var ovf_o)
    (Expr.group (sig := [s13OvfSig isBeyond])
      (fun _J_ovf => Blocks.cons (fun x =>
        match isBeyond, x with
        | true, (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ovf_p, rw, oth, cr, ri, ()) =>
          s13PostLpOvfExpr true c nl64 not_lit off_o end_o Bo Lo
            te_p un_p uf_p tk_p p_p q_p di_p 0#64 ovf_p rw oth cr ri
        | false, (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p, rw, oth, cr, ri, ()) =>
          s13PostLpOvfExpr false c nl64 not_lit off_o end_o Bo Lo
            te_p un_p uf_p tk_p p_p q_p di_p brk_p ovf_p rw oth cr ri)
        Blocks.nil)
      (fun J_ovf =>
        s13LpLoopExpr isBeyond c.hdr ignore_ref c.pVals c.pWstk c.pArena c.pLevel c.pReason
          c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim two_cv cur_lvl32
          rec_ph bigbig not_lit nl_lvl te_o un_o uf_o tk_o p_o q_o end_o di_o
          (if isBeyond then Arg.imm 0 else Arg.var brk_o) J_ovf.1))
    (Expr.jump Bo (Arg.var te_o, Arg.var un_o, Arg.var uf_o, Arg.var tk_o,
      Arg.var off_o, Arg.var p_o, Arg.var q_o, Arg.var end_o,
      Arg.var di_o, if isBeyond then Arg.imm 0 else Arg.var brk_o, Arg.var ovf_o, ()))

/-- Shared `while (ovf)` + watch compaction + final flush / exit AST builder parameterized by
`isBeyond : Bool`. -/
@[expose] def s13OvfLoopExpr
    (c : FullCfg) (isBeyond : Bool) (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (dlim : Val i64) (ignore_ref : Arg Val i64) (two_cv : Val i64)
    (cur_lvl32 not_lit nl_lvl : Val i32) (rec_ph bigbig : Val Ty.bool)
    (nl64 prop_v fuel1 te0 un0 uf0 tk0 off0 end0 : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]])
    (fun _Bo =>
      Blocks.cons (fun b =>
        s13CompactAndPostExpr J_out c.hdr c.pWstk c.pWvec nl64 prop_v fuel1
          b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1
          b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.2.1) Blocks.nil)
    (fun Bo =>
      Expr.group (sig := [s13LoSig isBeyond])
        (fun Lo =>
          Blocks.cons (fun o =>
            match isBeyond, o with
            | true, (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, ovf_o, ()) =>
              s13OvfLoopBody c true Bo.1 Lo.1 dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
                rec_ph bigbig nl64 te_o un_o uf_o tk_o off_o p_o q_o end_o di_o 0#64 ovf_o
            | false, (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o, ovf_o, ()) =>
              s13OvfLoopBody c false Bo.1 Lo.1 dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
                rec_ph bigbig nl64 te_o un_o uf_o tk_o off_o p_o q_o end_o di_o brk_o ovf_o)
            Blocks.nil)
        (fun Lo =>
          s13LoJump isBeyond Lo.1 (Arg.var te0) (Arg.var un0) (Arg.var uf0) (Arg.var tk0)
            (Arg.var off0) (Arg.var off0) (Arg.var off0) (Arg.var end0)
            (Arg.imm 0) (Arg.imm 0) (Arg.imm true)))

/-! ## 2. `while (ovf)` Loop-Body Theorem -/

private theorem s13_ovf_exit_to_join {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext1 : List (BitVec 64)} {s s_disk s_base sem_o : FullState}
    {ign_v off_o p_o end_o te_p un_p uf_p p_p q_p di_p brk_p ri_p : BitVec 64}
    {not_lit rw_p oth_p cr_p : BitVec 32} {ovf_p : Bool} {R : Mem 64 → Prop} {m' : Mem 64}
    (hd0_o : c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed)
    (hoom_o2 : sem_o.core.oom = 0#64)
    (hbody : S13OvfBody isBeyond c F0 F_cur ign_v s_disk
      { s_base with scratch := { s_base.scratch with delayed := sem_o.scratch.delayed } }
      sem_o not_lit off_o end_o 0#64 (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)
      te_p un_p uf_p 0#64 p_p q_p di_p brk_p ovf_p rw_p oth_p cr_p ri_p m')
    (hp_le : p_o.toNat ≤ p_p.toNat) (hflag_lt : ovf_p = true → p_o.toNat < p_p.toNat) :
    ∃ (sem_p : FullState) (dlen_p : Nat),
      PropLitInv c F0 F_cur
        { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
        sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat ∧
      di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
      DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
      (c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed) ∧
      p_o.toNat ≤ p_p.toNat ∧ s_base.core.trail_end ≤ sem_p.core.trail_end ∧
      te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
      uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
      (ovf_p = false → (brk_p = 0#64 → p_p = end_o ∧ S13ConflEq sem_o.core sem_p.core) ∧
        (brk_p = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_p.core) ∧
        (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
      (ovf_p = true → brk_p = 0#64 ∧ S13ConflEq sem_o.core sem_p.core ∧
        2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
        end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
        cr_p.toNat < 0x80000000 ∧ cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
        fullArenaClauseGarbCore sem_p.core cr_p.toNat = false ∧
        cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core cr_p.toNat ≤ sem_p.core.arena_len ∧
        oth_p.toNat < 2 * sem_p.core.cur_vars ∧
        rw_p.toNat < 2 * sem_p.core.cur_vars ∧ rw_p.toNat ≠ not_lit.toNat ∧
        2 ≤ ri_p.toNat ∧ ri_p.toNat < fullArenaClauseSizeCore sem_p.core cr_p.toNat ∧
        (∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ oth_p = l0' ^^^ l1' ^^^ not_lit ∧
          sem_p.core.arena[cr_p.toNat + 3]? = some l0' ∧
          sem_p.core.arena[cr_p.toNat + 4]? = some l1') ∧
        sem_p.core.arena[cr_p.toNat + 3 + ri_p.toNat]? = some rw_p) ∧
      (FullMem c (fastPropMem s_disk sem_p) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m' := by
  rcases hbody with ⟨sem_p, del_p, dlen_p, hmp, hpi_p, hdok_p, hd0_p, hte_p, hun_p, huf_p,
    hdi_p, hdl_p, _hcv_p, _hpr_p, _hsdl_p, _hstk_p, hoom_p, _hsd_len', _hsd_cv', _hsd_pr', htail⟩
  have hdel_eq : del_p = sem_p.scratch.delayed :=
    (congrArg (fun x => x.delayed) hpi_p.sc_eq).symm
  have hpi_p' : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
      sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat := by
    simpa only [hdel_eq] using hpi_p
  have hdok_b : DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat := by
    have hdok' : DelayedWatchesOk sem_p.core sem_p.scratch.delayed dlen_p not_lit.toNat := by
      simpa only [hdel_eq] using hdok_p
    exact delayedWatchesOk_congr hdok' (hpi_p'.ag.get FullCoreState.cur_vars).symm
      (fun r hr => hpi_p'.perm.2.1 ▸ hr)
  refine ⟨sem_p, dlen_p, hpi_p', hdi_p, hdl_p, hdok_b,
    (fun h0 => hdel_eq.symm.trans ((hd0_p h0).trans (hd0_o h0))), hp_le, hpi_p'.tr.1,
    hte_p.symm, hun_p.symm, huf_p.symm, hoom_p.trans hoom_o2, ?_, ?_, hmp⟩
  · intro hov
    simp only [hov, Bool.false_eq_true, ↓reduceIte] at htail
    by_cases h0 : brk_p = 0#64
    · simp only [h0, ↓reduceIte] at htail
      exact ⟨fun _ => htail, fun h1 => absurd h0 (by rw [h1]; decide), Or.inl h0⟩
    · simp only [h0, ↓reduceIte] at htail
      exact ⟨fun hb => absurd hb h0, fun _ => ⟨htail.1, htail.2.2⟩, Or.inr htail.2.1⟩
  · intro hov
    simp only [hov, ↓reduceIte] at htail
    obtain ⟨rfl, hq_pp2, hct_p, hrw_lt, hrw_ne, hcr_lt, hcr_ref, hng, hsz3, hfit, hri2, hri_lt,
      hwt_p, _hm_oth⟩ := htail
    obtain ⟨l0', l1', har3, har4, hwt, hoth, har_ri⟩ := hwt_p
    have hlt_flag := hflag_lt hov
    have hp_end := hpi_p'.sw.p_le_end
    have hq_ge := hpi_p'.sw.q_ge
    have hc_mem (idx : Nat) (hidx : idx < 2) {lit : BitVec 32}
        (hlit : sem_p.core.arena[cr_p.toNat + 3 + idx]? = some lit) :
        lit.toNat < 2 * sem_p.core.cur_vars := by
      have hmem : lit.toNat ∈ fullArenaClauseLitsCore (withEmptyWatchesCore c sem_p.core)
          cr_p.toNat := by
        unfold fullArenaClauseLitsCore
        refine List.mem_map_of_mem ?_
        have hsz_lt : idx < fullArenaClauseSizeCore (withEmptyWatchesCore c sem_p.core)
            cr_p.toNat := by
          change idx < fullArenaClauseSizeCore sem_p.core cr_p.toNat
          exact Nat.lt_of_lt_of_le hidx (Nat.le_trans (by decide) hsz3)
        exact List.mem_of_getElem? (i := idx) (by
          rw [List.getElem?_take_of_lt hsz_lt, List.getElem?_drop]
          simpa only [withEmptyWatchesCore] using hlit)
      exact hpi_p'.nw.arena.lits_lt cr_p.toNat hcr_ref hng lit.toNat hmem
    have hl0_lt := hc_mem 0 (by omega) (by simpa only [Nat.add_zero] using har3)
    have hl1_lt := hc_mem 1 (by omega) (by simpa only [Nat.add_assoc] using har4)
    have hoth_lt : oth_p.toNat < 2 * sem_p.core.cur_vars := by
      rcases hwt with hl0 | hl1
      · have heq : oth_p = l1' := by
          rw [hoth, hl0, BitVec.xor_comm not_lit l1', BitVec.xor_assoc, BitVec.xor_self,
            BitVec.xor_zero]
        rw [heq]; exact hl1_lt
      · have heq : oth_p = l0' := by
          rw [hoth, hl1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        rw [heq]; exact hl0_lt
    exact ⟨rfl, hct_p, by omega, hq_pp2, by omega, hcr_lt, hcr_ref, hng, hfit, hoth_lt, hrw_lt,
      hrw_ne, hri2, hri_lt, ⟨l0', l1', hwt, hoth, har3, har4⟩, har_ri⟩

theorem s13_ovf_loop_body_wp {Γ : Env} {isBeyond rec_ph bigbig : Bool} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ext1 : List (BitVec 64)}
    {s sem s_base s_disk sem_o : FullState} {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {ignore_ref : Arg Val i64} {ign_v nl64 two_cv dlim : BitVec 64}
    {te_o un_o uf_o tk_o off_o p_o q_o end_o di_o brk_o : BitVec 64} {ovf_o : Bool} {dlen_o : Nat}
    {Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    {Lo : Cont (s13LoSig isBeyond)} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mo : Mem 64}
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" fidPropFlushDelSpec)
    (_hcfg : FullM6HdrCfgOk c) (hlen0 : s.LengthsOk c)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (hlen_o : sem.LengthsOk c) (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hd0_sem : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hign_val : ignore_ref = Arg.imm ign_v ∨ ignore_ref = Arg.var ign_v)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem.core.cur_vars) (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat)) (hnl64_idx : nl64.toNat = 2 * not_lit.toNat)
    (hnl_sbase : ∀ k : FullCoreState, FullTrailExt s_base.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl) (hdlim : dlim.toNat = 3 * c.delayed_cap)
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
          xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
        (isBeyond = true → S13ConflEq s.core sem_b.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
          PropLitConfl F_cur ign_v sem_b.core ∧ sem_b.core.oom = 0#64) ∧
        (if isBeyond then (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 2#64)
         else (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64 ∨
           xs.2.2.2.2.2.2.2.2.2.1 = 2#64)) ∧
        (FullMem c (fastPropMem s_disk sem_b) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mb) →
      Bo xs mb)
    (hih : ∀ rem xs m,
      rem < (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) →
      (∃ (sem_o' : FullState) (dlen_o' : Nat),
        (isBeyond = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64) ∧
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
        (isBeyond = true → S13ConflEq s.core sem_o'.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∧
          sem_o'.core.oom = 0#64 ∧
          (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type)) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = false →
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_o'.core.oom = 0#64 ∧
            (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type) ∧
            xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
            PropLitConfl F_cur ign_v sem_o'.core ∧ sem_o'.core.oom = 0#64) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64)) ∧
        (FullMem c (fastPropMem s_disk sem_o') ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m) →
      Lo (s13LoTup isBeyond xs) m)
    (hbrk_ib : isBeyond = true → brk_o = 0#64)
    (hpi_o : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_o.scratch.delayed } }
      sem_o not_lit.toNat off_o.toNat q_o.toNat p_o.toNat end_o.toNat)
    (hdi_o : di_o.toNat = 3 * dlen_o) (hdl_o : dlen_o ≤ c.delayed_cap)
    (hdok_o : DelayedWatchesOk s_base.core sem_o.scratch.delayed dlen_o not_lit.toNat)
    (hd0_o : c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed)
    (hte_o : te_o.toNat = sem_o.core.trail_end) (hun_o : un_o = sem_o.core.unassigned)
    (huf_o : uf_o = sem_o.core.unflushed) (hbcf_o2 : isBeyond = true → S13ConflEq s.core sem_o.core)
    (hov_t : ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
      (isBeyond = false → sem_o.core.confl_type = s.core.confl_type))
    (hov_f : ovf_o = false →
      (brk_o = 0#64 → sem_o.core.oom = 0#64 ∧
        (isBeyond = false → sem_o.core.confl_type = s.core.confl_type) ∧ p_o = end_o) ∧
      (brk_o = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_o.core ∧
        sem_o.core.oom = 0#64) ∧
      (brk_o = 0#64 ∨ brk_o = 1#64))
    (hmo : (FullMem c (fastPropMem s_disk sem_o) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mo) :
    wp Γ Q X (s13OvfLoopBody c isBeyond Bo Lo dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
      rec_ph bigbig nl64 te_o un_o uf_o tk_o off_o p_o q_o end_o di_o brk_o ovf_o) mo := by
  have _ := hd0_sem
  have hsd_len : s_disk.LengthsOk c := by
    obtain ⟨te_mem, hs_d, htm, hpt⟩ := hs_disk
    subst hs_d; exact ⟨{ hlen0.core_ok with
      trail_end_le := Nat.le_trans htm (hcv_o ▸ hlen_o.core_ok.trail_end_le),
      propagated_le := hpt }, hlen0.scratch_ok⟩
  have hsd_cv : s_disk.core.cur_vars = s_base.core.cur_vars := by
    obtain ⟨_, hs_d, _⟩ := hs_disk; rw [hs_d, hs_base]; exact hcv_o.symm
  have hsd_pr : s_disk.core.propagated = s_base.core.propagated := by
    obtain ⟨_, hs_d, _⟩ := hs_disk; rw [hs_d, hs_base]
  unfold s13OvfLoopBody
  s13_hsplit
  · have hov_t_eq : ovf_o = true := hc
    obtain ⟨hbr0_o, hoom_o2, hct_o2⟩ := hov_t hov_t_eq
    clear hov_t hov_f hc
    s13_hsteps_nogrp
    refine wp_join_group
      (fun x mbp =>
        ∃ te_p un_p uf_p tk_p p_p q_p di_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p,
          x = s13OvfTup isBeyond (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
            ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ()) ∧
          (isBeyond = true → brk_p = 0#64) ∧
          ∃ (sem_p : FullState) (dlen_p : Nat),
            PropLitInv c F0 F_cur
              { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
              sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat ∧
            di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
            DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
            (c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed) ∧
            p_o.toNat ≤ p_p.toNat ∧ s_base.core.trail_end ≤ sem_p.core.trail_end ∧
            te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
            uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
            (ovf_p = false → (brk_p = 0#64 → p_p = end_o ∧
                S13ConflEq sem_o.core sem_p.core) ∧
              (brk_p = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_p.core) ∧
              (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
            (ovf_p = true → brk_p = 0#64 ∧ S13ConflEq sem_o.core sem_p.core ∧
              2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
              end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
              ovf_cr_p.toNat < 0x80000000 ∧ ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
              fullArenaClauseGarbCore sem_p.core ovf_cr_p.toNat = false ∧
              ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
                sem_p.core.arena_len ∧
              ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
              ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧ ovf_rw_p.toNat ≠ not_lit.toNat ∧
              2 ≤ ovf_ri_p.toNat ∧
              ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
              (∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧
                ovf_oth_p = l0' ^^^ l1' ^^^ not_lit ∧
                sem_p.core.arena[ovf_cr_p.toNat + 3]? = some l0' ∧
                sem_p.core.arena[ovf_cr_p.toNat + 4]? = some l1') ∧
              sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p) ∧
            (FullMem c (fastPropMem s_disk sem_p) ⋆
              (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mbp) ?_ ?_
    · rintro _ x mbp ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, rfl, hbrk_p_ib,
          sem_p, dlen_p, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hpo_le_pp, _hte_ge_p,
          hte_p, hun_p, huf_p, hoom_p, hnoov, hov_yes, hmbp⟩
      cases ovf_p
      · have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
        cases isBeyond
        · dsimp only [Blocks.get, s13OvfTup]; unfold s13PostLpOvfExpr
          refine wp_unroll_group fun _Js0 _hJs0 => ?_; s13_hsteps
          refine hih (end_o.toNat - p_p.toNat)
            (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, di_p, brk_p, false, ()) mbp
            (by simpa only [hov_t_eq, ↓reduceIte] using by omega)
            ⟨sem_p, dlen_p, fun h => absurd h (by decide), rfl, hpi_p, hdi_p, hdl_p, hdok_p,
              hd0_p, hte_p, hun_p, huf_p, fun h => absurd h (by decide),
              fun h => Bool.noConfusion h,
              fun _ => ⟨fun h0 => ⟨hoom_p, fun _ => ((hbrk0_fn h0).2.1).trans (hct_o2 rfl),
                  (hbrk0_fn h0).1⟩,
                fun h1 => let ⟨hb, hc⟩ := hbrk1_fn h1; ⟨hb, hc, hoom_p⟩, hbrk_disj⟩, hmbp⟩
        · obtain rfl := hbrk_p_ib rfl
          dsimp only [Blocks.get, s13OvfTup]; unfold s13PostLpOvfExpr
          refine wp_unroll_group fun _Js0 _hJs0 => ?_; s13_hsteps
          refine hih (end_o.toNat - p_p.toNat)
            (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, di_p, 0#64, false, ()) mbp
            (by simpa only [hov_t_eq, ↓reduceIte] using by omega)
            ⟨sem_p, dlen_p, fun _ => rfl, rfl, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hte_p, hun_p,
              huf_p,
              fun _ => s13ConflEq_trans ((hbrk0_fn (hbrk_disj.resolve_right
                (fun h1 => Bool.noConfusion (hbrk1_fn h1).1))).2) (hbcf_o2 rfl),
              fun h => Bool.noConfusion h,
              fun _ => ⟨fun _ => ⟨hoom_p, fun h => absurd h (by decide), (hbrk0_fn rfl).1⟩,
                fun h1 => let ⟨hb, hc⟩ := hbrk1_fn h1; ⟨hb, hc, hoom_p⟩, hbrk_disj⟩, hmbp⟩
      · obtain ⟨h_b0, h_cf, h_p2, h_qp2, h_dec, h_cr1, h_cr2, _h_ng, h_cr3, h_o1, h_r1, h_r2,
            h_ri2, h_ri3, h_wt, h_ar⟩ := hov_yes rfl
        have hnot_p : not_lit.toNat < 2 * sem_p.core.cur_vars :=
          (hpi_p.ag.get FullCoreState.cur_vars).symm ▸ (by rw [hs_base]; exact hnot_lt)
        cases isBeyond
        · dsimp only [Blocks.get, s13OvfTup]
          exact s13_post_lp_ovf_wp (isBeyond := false) (ovf_p := true) (sem := sem)
            (ign_v := ign_v)
            (R := m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R) hOvf hFlush
            (fun xs mb ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                h0, h1, hds, _hcf_b, hmb⟩ =>
              hBo xs mb ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                h0, fun hb => Bool.noConfusion hb, h1,
                by rcases hds with h | h | h <;> simp [h], hmb⟩)
            (fun rem xs m hlt ⟨sem_o', dlen_o', hr, hpi_o', hdi_o', hdl_o', hdok_o', hd0_o',
                hte_o', hun_o', huf_o', ht', hf', hm'⟩ =>
              hih rem xs m (by simpa only [hov_t_eq, ↓reduceIte] using hlt)
                ⟨sem_o', dlen_o', fun hb => Bool.noConfusion hb, hr, hpi_o', hdi_o', hdl_o',
                  hdok_o', hd0_o', hte_o', hun_o', huf_o', fun hb => Bool.noConfusion hb,
                  fun hbt => let ⟨t1, t2, t3⟩ := ht' hbt;
                    ⟨t1, t2, fun _ => t3.1.trans (hct_o2 rfl)⟩,
                  fun hb0 => let ⟨h0a, h0b, h0c⟩ := hf' hb0;
                    ⟨fun hx0 => let x := h0a hx0; ⟨x.1, fun _ => x.2.1.1.trans (hct_o2 rfl),
                      x.2.2⟩,
                     h0b, h0c⟩, hm'⟩)
            c.harena c.hwcap hsd_len hsd_cv hsd_pr hpo_le_pp hnot_p hnl64 hnl64_idx
            hpi_p.sw.off_eq.symm hpi_p hdi_p hdl_p hdok_p hd0_p hte_p hun_p huf_p hoom_p
            (fun h => Bool.noConfusion h)
            (fun _ => ⟨h_b0, h_cf, h_p2, h_qp2, h_dec, h_cr1, h_cr2, h_cr3, h_o1, h_r1, h_r2,
              h_ri2, h_ri3, h_wt, h_ar⟩) hmbp
        · obtain rfl := hbrk_p_ib rfl
          dsimp only [Blocks.get, s13OvfTup]
          exact s13_post_lp_ovf_wp (isBeyond := true) (ovf_p := true) (sem := sem)
            (ign_v := ign_v)
            (R := m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R) hOvf hFlush
            (fun xs mb ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                h0, h1, hds, hcf_b, hmb⟩ =>
              hBo xs mb ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                fun hb0 => let x := h0 hb0; ⟨x.1, fun hb => Bool.noConfusion hb, x.2.2⟩,
                fun hb => s13ConflEq_trans hcf_b (hbcf_o2 hb),
                fun hb1 => Bool.noConfusion (h1 hb1).1,
                by rcases hds with hds0 | hds1 | hds2
                   · exact Or.inl hds0
                   · exact absurd (h1 hds1).1 (by decide)
                   · exact Or.inr hds2, hmb⟩)
            (fun rem xs m hlt ⟨sem_o', dlen_o', hr, hpi_o', hdi_o', hdl_o', hdok_o', hd0_o',
                hte_o', hun_o', huf_o', ht', hf', hm'⟩ =>
              hih rem xs m (by simpa only [hov_t_eq, ↓reduceIte] using hlt)
                ⟨sem_o', dlen_o',
                  fun _ => by
                    by_cases hov' : xs.2.2.2.2.2.2.2.2.2.2.1 = true
                    · exact (ht' hov').1
                    · have hovf' : xs.2.2.2.2.2.2.2.2.2.2.1 = false :=
                        Bool.eq_false_iff.mpr hov'
                      have ⟨_, h1b, hdb⟩ := hf' hovf'
                      exact hdb.resolve_right (fun h1 => Bool.noConfusion (h1b h1).1),
                  hr, hpi_o', hdi_o', hdl_o', hdok_o', hd0_o', hte_o', hun_o', huf_o',
                  (fun _ => by
                    by_cases hov' : xs.2.2.2.2.2.2.2.2.2.2.1 = true
                    · exact s13ConflEq_trans (ht' hov').2.2 (hbcf_o2 rfl)
                    · have hovf' : xs.2.2.2.2.2.2.2.2.2.2.1 = false :=
                        Bool.eq_false_iff.mpr hov'
                      have ⟨h0b, h1b, hdb⟩ := hf' hovf'
                      exact s13ConflEq_trans
                        (h0b (hdb.resolve_right (fun h1 => Bool.noConfusion (h1b h1).1))).2.1
                        (hbcf_o2 rfl)),
                  fun hbt => let x := ht' hbt; ⟨x.1, x.2.1, fun hb => Bool.noConfusion hb⟩,
                  fun hb0 => let ⟨h0a, h0b, h0c⟩ := hf' hb0;
                    ⟨fun hx0 => let x := h0a hx0; ⟨x.1, fun hb => Bool.noConfusion hb, x.2.2⟩,
                     fun hx1 => Bool.noConfusion (h0b hx1).1,
                     Or.inl (h0c.resolve_right (fun h1 => Bool.noConfusion (h0b h1).1))⟩, hm'⟩)
            c.harena c.hwcap hsd_len hsd_cv hsd_pr hpo_le_pp hnot_p hnl64 hnl64_idx
            hpi_p.sw.off_eq.symm hpi_p hdi_p hdl_p hdok_p hd0_p hte_p hun_p huf_p hoom_p
            (fun h => Bool.noConfusion h)
            (fun _ => ⟨h_b0, h_cf, h_p2, h_qp2, h_dec, h_cr1, h_cr2, h_cr3, h_o1, h_r1, h_r2,
              h_ri2, h_ri3, h_wt, h_ar⟩) hmbp
    · intro J_ovf hJ_ovf
      have hnot_o : not_lit.toNat < 2 * sem_o.core.cur_vars := by
        rw [(hpi_o.ag.get FullCoreState.cur_vars), hs_base]; exact hnot_lt
      have hcl32_o : sem_o.core.cur_level < 2 ^ 32 := by
        rw [hpi_o.ag.get FullCoreState.cur_level, hs_base]; exact hcl32
      have hcl_cur_o : cur_lvl32.toNat = sem_o.core.cur_level := by
        rw [hcur_lvl, hpi_o.ag.get FullCoreState.cur_level, hs_base,
          m7_bv32_ofNat_toNat_lt hcl32]
      have hdok_o_sem : DelayedWatchesOk sem_o.core sem_o.scratch.delayed dlen_o not_lit.toNat :=
        delayedWatchesOk_congr hdok_o (hpi_o.ag.get FullCoreState.cur_vars)
          (fun r hr => hpi_o.perm.2.1.symm ▸ hr)
      have hsd_pr_o : sem_o.core.propagated ≤ s_disk.core.trail_end := by
        obtain ⟨_, hs_d, _, hpt⟩ := hs_disk
        rw [hs_d, (hpi_o.ag.get FullCoreState.propagated), hs_base]; exact hpt
      have hinv_o : S13LpInv c F0 F_cur s_disk { s_base with scratch :=
          { s_base.scratch with delayed := sem_o.scratch.delayed } } sem_o sem_o not_lit off_o
          end_o te_o un_o uf_o tk_o p_o q_o di_o mo (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R) :=
        ⟨sem_o.scratch.delayed, dlen_o, hmo, hpi_o, hdok_o_sem, (fun _ => rfl), hte_o.symm,
          hun_o.symm, huf_o.symm, hdi_o, hdl_o, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩,
          hsd_len, hsd_cv.trans (hpi_o.ag.get FullCoreState.cur_vars).symm, hsd_pr_o⟩
      have hbrk_eval : (if isBeyond then Arg.imm 0 else Arg.var brk_o : Arg Val i64) =
          Arg.imm 0#64 ∨ (if isBeyond then Arg.imm 0 else Arg.var brk_o : Arg Val i64) =
          Arg.var (0#64 : Val i64) := by
        cases isBeyond
        · exact Or.inr (congrArg (fun v : Val i64 => Arg.var v) hbr0_o)
        · exact Or.inl rfl
      refine s13_lp_loop_wp hign_val hbrk_eval hinv_o hnot_o
        (by rw [htwo_cv, (hpi_o.ag.get FullCoreState.cur_vars), hs_base])
        hcl_cur_o (fun k htr_k => hnl_sbase k htr_k) hdlim rfl ?_
      intro xs m' hexit hp_le hflag_lt
      cases isBeyond
      · rcases xs with ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
            rw_p, oth_p, cr_p, ri_p, ⟨⟩⟩
        dsimp only [S13OvfExitPred, s13OvfP, s13OvfFlag] at hexit hp_le hflag_lt
        have hj := s13_ovf_exit_to_join hd0_o hoom_o2 hexit hp_le hflag_lt
        exact hJ_ovf _ m' ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
          rw_p, oth_p, cr_p, ri_p, rfl, (fun h => Bool.noConfusion h), hj⟩
      · rcases xs with ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ovf_p,
            rw_p, oth_p, cr_p, ri_p, ⟨⟩⟩
        dsimp only [S13OvfExitPred, s13OvfP, s13OvfFlag] at hexit hp_le hflag_lt
        have hj := s13_ovf_exit_to_join hd0_o hoom_o2 hexit hp_le hflag_lt
        exact hJ_ovf _ m' ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, 0#64, ovf_p,
          rw_p, oth_p, cr_p, ri_p, rfl, (fun _ => rfl), hj⟩
  · have hovf_f_eq : ovf_o = false := by revert hc; cases ovf_o <;> simp
    have ⟨h0, h1, hcs⟩ := hov_f hovf_f_eq
    cases isBeyond
    · s13_hsteps
      exact hBo _ mo ⟨sem_o, dlen_o, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o, hte_o, hun_o, huf_o,
        h0, hbcf_o2, h1, by rcases hcs with rfl | rfl <;> simp, hmo⟩
    · s13_hsteps
      exact hBo _ mo ⟨sem_o, dlen_o, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o, hte_o, hun_o, huf_o,
        (fun _ => h0 (hbrk_ib rfl)), hbcf_o2, (fun h => by simp at h), Or.inl rfl, hmo⟩

private structure S13OvfSt where
  sem_o : FullState
  dlen_o : Nat
  te_o : BitVec 64
  un_o : BitVec 64
  uf_o : BitVec 64
  tk_o : BitVec 64
  off_o : BitVec 64
  p_o : BitVec 64
  q_o : BitVec 64
  end_o : BitVec 64
  di_o : BitVec 64
  brk_o : BitVec 64
  ovf_o : Bool

private def s13OvfProj (isBeyond : Bool) (st : S13OvfSt) :
    Tup Val (s13LoSig isBeyond) :=
  match isBeyond with
  | true => (st.te_o, st.un_o, st.uf_o, st.tk_o, st.off_o, st.p_o, st.q_o, st.end_o,
      st.di_o, st.ovf_o, ())
  | false => (st.te_o, st.un_o, st.uf_o, st.tk_o, st.off_o, st.p_o, st.q_o, st.end_o,
      st.di_o, st.brk_o, st.ovf_o, ())

/-- Combined `while (ovf)` + compact + delayed flush + ticks/return WP for `s13OvfLoopExpr`. -/
theorem s13_ovf_loop_wp {Γ : Env} {isBeyond rec_ph bigbig : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem s_base s_disk : FullState} {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {ignore_ref : Arg Val i64}
    {ign_v nl64 two_cv dlim prop_v fuel1 te0 un0 uf0 tk0 off0 end0 : BitVec 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m0 : Mem 64}
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" fidPropFlushDelSpec)
    (hAddTicks : Γ.Has "m6_hdr_add_ticks" m6HdrAddTicksSpec)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ign_v R Q)
    (hJ_out : ∀ {te_b un_b uf_b tk_b : BitVec 64} (sem_next : FullState) (te_mc : Nat)
      (mc0 : Mem 64),
      sem_next.LengthsOk c → FullWitnessInv c F0 F_cur sem_next.core →
      FullTrailExt s.core sem_next.core → FullTrailRsnsPres s.core sem_next.core →
      FullArenaPermEq s.core sem_next.core → AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 → sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b → sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      (isBeyond = false → sem_next.core.confl_type = s.core.confl_type) →
      (isBeyond = true → S13ConflEq s.core sem_next.core) →
      sem_next.core.dense_mode = 0#64 → sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level → sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated → te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc → S13Scr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R)
        mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hwc : c.wcap < 2 * dimacsBound) (hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (hlen_o : sem.LengthsOk c)
    (htr_o : FullTrailExt s.core sem.core) (hrsns_o : FullTrailRsnsPres s.core sem.core)
    (hperm_o : FullArenaPermEq s.core sem.core) (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars) (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing) (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : S13Scr s sem) (hd0_sem : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end) (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hign_val : ignore_ref = Arg.imm ign_v ∨ ignore_ref = Arg.var ign_v)
    (htwo_cv : two_cv.toNat = 2 * sem.core.cur_vars) (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat)) (hnl64_idx : nl64.toNat = 2 * not_lit.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hnl_sbase : ∀ k : FullCoreState, FullTrailExt s_base.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl) (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hpi_0 : PropLitInv c F0 F_cur s_base s_base
      not_lit.toNat off0.toNat off0.toNat off0.toNat end0.toNat)
    (hte0 : te0.toNat = sem.core.trail_end) (hun0 : un0 = sem.core.unassigned)
    (huf0 : uf0 = sem.core.unflushed) (hoom0 : sem.core.oom = 0#64)
    (hct0 : isBeyond = false → sem.core.confl_type = s.core.confl_type)
    (hcf0 : isBeyond = true → S13ConflEq s.core sem.core)
    (hm0 : (FullMem c (fastPropMem s_disk s_base) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m0) :
    wp Γ Q X (s13OvfLoopExpr c isBeyond J_out dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
      rec_ph bigbig nl64 prop_v fuel1 te0 un0 uf0 tk0 off0 end0) m0 := by
  unfold s13OvfLoopExpr
  refine wp_join_group
    (fun (b : Tup Val [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]) mb =>
      ∃ (sem_b : FullState) (dlen_b : Nat),
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
          sem_b not_lit.toNat b.2.2.2.2.1.toNat b.2.2.2.2.2.2.1.toNat
          b.2.2.2.2.2.1.toNat b.2.2.2.2.2.2.2.1.toNat ∧
        b.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
        b.1.toNat = sem_b.core.trail_end ∧ b.2.1 = sem_b.core.unassigned ∧
        b.2.2.1 = sem_b.core.unflushed ∧
        (b.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_b.core.oom = 0#64 ∧
          (isBeyond = false → sem_b.core.confl_type = s.core.confl_type) ∧
          b.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.1) ∧
        (isBeyond = true → S13ConflEq s.core sem_b.core) ∧
        (b.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
          PropLitConfl F_cur ign_v sem_b.core ∧ sem_b.core.oom = 0#64) ∧
        (if isBeyond then (b.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ b.2.2.2.2.2.2.2.2.2.1 = 2#64)
         else (b.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ b.2.2.2.2.2.2.2.2.2.1 = 1#64 ∨
           b.2.2.2.2.2.2.2.2.2.1 = 2#64)) ∧
        (FullMem c (fastPropMem s_disk sem_b) ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mb) ?_ ?_
  · rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, _ovf_b, ⟨⟩⟩ mb
      ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b, hbr0, hcf_b, hbr1,
        hbr_cases, hmb⟩
    exact s13_compact_post_wp (isBeyond := isBeyond) (sem_b := sem_b) (not_lit := not_lit)
      (ignore_ref := ign_v) (dlen_b := dlen_b) hFlush hAddTicks hQ
      (fun sem_next te_mc mc0 => hJ_out sem_next te_mc mc0)
      hcfg hext1 hw2b1 hwc hmaxv hlen0 hpr_lt hs_base hfuel1 hs_disk htr_o hrsns_o hperm_o hag_o
      hcv_o hcl_o hprob_o halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge hnl64 hnot_lt
      hdense_b hpi_b hdi_b hdl_b hdok_b hd0_b hte_b hun_b huf_b
      (fun h => let x := hbr0 h; ⟨x.1, x.2.1⟩) hcf_b hbr1 hbr_cases hmb
  · intro Bo hBo
    let InvLo : S13OvfSt → Mem 64 → Prop := fun st m =>
      (isBeyond = true → st.brk_o = 0#64) ∧
      PropLitInv c F0 F_cur
        { s_base with scratch := { s_base.scratch with delayed := st.sem_o.scratch.delayed } }
        st.sem_o not_lit.toNat st.off_o.toNat st.q_o.toNat st.p_o.toNat st.end_o.toNat ∧
      st.di_o.toNat = 3 * st.dlen_o ∧ st.dlen_o ≤ c.delayed_cap ∧
      DelayedWatchesOk s_base.core st.sem_o.scratch.delayed st.dlen_o not_lit.toNat ∧
      (c.delayed_cap = 0 → st.sem_o.scratch.delayed = s.scratch.delayed) ∧
      st.te_o.toNat = st.sem_o.core.trail_end ∧ st.un_o = st.sem_o.core.unassigned ∧
      st.uf_o = st.sem_o.core.unflushed ∧ (isBeyond = true → S13ConflEq s.core st.sem_o.core) ∧
      (st.ovf_o = true → st.brk_o = 0#64 ∧ st.sem_o.core.oom = 0#64 ∧
        (isBeyond = false → st.sem_o.core.confl_type = s.core.confl_type)) ∧
      (st.ovf_o = false →
        (st.brk_o = 0#64 → st.sem_o.core.oom = 0#64 ∧
          (isBeyond = false → st.sem_o.core.confl_type = s.core.confl_type) ∧
          st.p_o = st.end_o) ∧
        (st.brk_o = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v st.sem_o.core ∧
          st.sem_o.core.oom = 0#64) ∧
        (st.brk_o = 0#64 ∨ st.brk_o = 1#64)) ∧
      (FullMem c (fastPropMem s_disk st.sem_o) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m
    let μLo : S13OvfSt → Nat := fun st =>
      (st.end_o.toNat - st.p_o.toNat) + (if st.ovf_o then 1 else 0)
    refine wp_while_state (s13OvfProj isBeyond) μLo InvLo ?_ ?_
    · intro Lo hLo
      let st0 : S13OvfSt :=
        ⟨s_base, 0, te0, un0, uf0, tk0, off0, off0, off0, end0, 0#64, 0#64, true⟩
      have hsb_d0 : c.delayed_cap = 0 → s_base.scratch.delayed = s.scratch.delayed := by
        subst hs_base; exact hd0_sem
      have hsb_te : te0.toNat = s_base.core.trail_end := by subst hs_base; exact hte0
      have hsb_un : un0 = s_base.core.unassigned := by subst hs_base; exact hun0
      have hsb_uf : uf0 = s_base.core.unflushed := by subst hs_base; exact huf0
      have hsb_oom : s_base.core.oom = 0#64 := by subst hs_base; exact hoom0
      have hsb_ct : isBeyond = false → s_base.core.confl_type = s.core.confl_type := by
        subst hs_base; exact hct0
      have hsb_cf : isBeyond = true → S13ConflEq s.core s_base.core := by
        subst hs_base; exact hcf0
      cases isBeyond
      · dsimp only [s13LoJump]; s13_hsteps
        exact hLo st0 m0 ⟨fun h => Bool.noConfusion h, hpi_0, rfl, Nat.zero_le _,
          fun _ hj => absurd hj (Nat.not_lt_zero _), hsb_d0, hsb_te, hsb_un, hsb_uf,
          fun h => Bool.noConfusion h, fun _ => ⟨rfl, hsb_oom, hsb_ct⟩,
          fun h => Bool.noConfusion h, hm0⟩
      · dsimp only [s13LoJump]; s13_hsteps
        exact hLo st0 m0 ⟨fun _ => rfl, hpi_0, rfl, Nat.zero_le _,
          fun _ hj => absurd hj (Nat.not_lt_zero _), hsb_d0, hsb_te, hsb_un, hsb_uf,
          hsb_cf, fun _ => ⟨rfl, hsb_oom, fun h => Bool.noConfusion h⟩,
          fun h => Bool.noConfusion h, hm0⟩
    · intro Lo st m' ⟨hbrk_ib, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o, hte_o, hun_o, huf_o, hbcf_o2,
        hov_t, hov_f, hmo⟩ hih
      cases isBeyond
      · dsimp only [Blocks.get, s13OvfProj]
        refine s13_ovf_loop_body_wp hOvf hFlush hcfg hlen0 hs_base hs_disk hlen_o hcv_o
          hd0_sem hign_val hnot_lt htwo_cv hcl32 hcur_lvl hnl64 hnl64_idx hnl_sbase hdlim
          hBo (fun rem xs m hlt ⟨sem_o', dlen_o', _hbrk_ib', hr, hpi_o', hdi_o', hdl_o', hdok_o',
            hd0_o', hte_o', hun_o', huf_o', _hbcf_o2', ht', hf', hm'⟩ => by
            rcases xs with ⟨te', un', uf', tk', off', p', q', end', di', brk', ovf', ⟨⟩⟩
            dsimp only [s13LoTup]
            let st' : S13OvfSt :=
              ⟨sem_o', dlen_o', te', un', uf', tk', off', p', q', end', di', brk', ovf'⟩
            exact hih st' m (by dsimp only [μLo, st']; dsimp only at hr; rw [← hr]; exact hlt)
              ⟨fun h => Bool.noConfusion h, hpi_o', hdi_o', hdl_o', hdok_o', hd0_o', hte_o',
                hun_o', huf_o', fun h => Bool.noConfusion h, ht', hf', hm'⟩)
          hbrk_ib hpi_o hdi_o hdl_o hdok_o hd0_o hte_o hun_o huf_o hbcf_o2 hov_t hov_f hmo
      · dsimp only [Blocks.get, s13OvfProj]
        have hbr0_st := hbrk_ib rfl
        rw [hbr0_st] at hov_t hov_f
        refine s13_ovf_loop_body_wp hOvf hFlush hcfg hlen0 hs_base hs_disk hlen_o hcv_o
          hd0_sem hign_val hnot_lt htwo_cv hcl32 hcur_lvl hnl64 hnl64_idx hnl_sbase hdlim
          hBo (fun rem xs m hlt ⟨sem_o', dlen_o', hbrk_ib', hr, hpi_o', hdi_o', hdl_o', hdok_o',
            hd0_o', hte_o', hun_o', huf_o', hbcf_o2', ht', hf', hm'⟩ => by
            rcases xs with ⟨te', un', uf', tk', off', p', q', end', di', brk', ovf', ⟨⟩⟩
            dsimp only [s13LoTup]
            let st' : S13OvfSt :=
              ⟨sem_o', dlen_o', te', un', uf', tk', off', p', q', end', di', 0#64, ovf'⟩
            have hbr0' : brk' = 0#64 := hbrk_ib' rfl
            rw [hbr0'] at ht' hf'
            exact hih st' m (by dsimp only [μLo, st']; dsimp only at hr; rw [← hr]; exact hlt)
              ⟨fun _ => rfl, hpi_o', hdi_o', hdl_o', hdok_o', hd0_o', hte_o', hun_o', huf_o',
                hbcf_o2', ht', hf', hm'⟩)
          (fun _ => rfl) hpi_o hdi_o hdl_o hdok_o hd0_o hte_o hun_o huf_o hbcf_o2 hov_t hov_f hmo

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
