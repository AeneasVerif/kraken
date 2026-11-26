/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2a
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1c
import all LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0

/-!
# Kissat Fidelity Delayed-Watch BCP Proofs — Part 2d (Post-Scan Overflow, Compaction, \& Exits)

Plain `public section` (`@[expose]` ONLY on non-recursive concrete AST `Expr` builders, `0`
`import all`). Defines the outer-loop framing mask and spec continuation of
`full_propagate_ignore_fid`, the post-scan AST builders (overflow flush + cold push + rebase,
compaction, final delayed-watch flush, exits), and proves their WPs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fid_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "fid_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "fid_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Spec Continuation, Framing Mask, \& Exit Packaging -/

/-- Framing mask for `full_propagate_ignore_fid`: every field it may touch. -/
abbrev fidCoreMask (t : FullCoreState) : FullCoreState :=
  { t with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    trail_end := 0, propagated := 0, unassigned := 0#64, unflushed := 0#64,
    wvec := [], arena := [], wstk := [], wlen := 0, wusable := 0#64, fuel := 0#64,
    confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64,
    oom := 0#64 }

theorem fid_agrees_upd_prop_fuel {a b : FullCoreState} {p : Nat} {f : BitVec 64}
    (h : AgreesExcept fidCoreMask a b) :
    AgreesExcept fidCoreMask a { b with propagated := p, fuel := f } := by
  unfold AgreesExcept fidCoreMask at h ⊢; exact h

/-- Postcondition continuation of `FullM6BcpS15.fullPropagateIgnoreS15Spec`. -/
abbrev FidHQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (ignore_ref : BitVec 64) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (vals' : List (BitVec 8))
    (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
    (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
    (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (delayed' : List (BitVec 32))
    (m' : Mem 64),
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
            wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch :=
          { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullPropDecSpecs.FullTrailExt s.core s'.core →
    FullPropDecSpecs.FullArenaPermEq s.core s'.core →
    (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
    fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
    (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
      (s.core.oom = 0#64 → oom' = 0#64) ∧
      (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
    (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
      (ctype' = 2#64 → cref' ≠ ignore_ref)) →
    (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
    (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Scratch-frame shape: only `search_ticks`, `wsort`, `phases`, and `delayed` may change. -/
abbrev FidScr (s0 s1 : FullState) : Prop :=
  s1.scratch = { s0.scratch with
    search_ticks := s1.scratch.search_ticks, wsort := s1.scratch.wsort,
    phases := s1.scratch.phases, delayed := s1.scratch.delayed }

theorem fid_scratch_trans {s0 s1 s2 : FullState} (h01 : FidScr s0 s1) (h12 : FidScr s1 s2) :
    FidScr s0 s2 := by
  unfold FidScr at *; rw [h12, h01]

theorem fid_scr_of_pi {s0 s_pi st : FullState}
    (hpi : st.scratch = { s_pi.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases })
    (h0 : FidScr s0 s_pi) : FidScr s0 st := by
  unfold FidScr at *; rw [hpi, h0]

theorem fid_core_eq_of_agrees (s sem : FullCoreState) (h : AgreesExcept fidCoreMask s sem) :
    { s with
      unassigned := sem.unassigned, wlen := sem.wlen, wusable := sem.wusable,
      unflushed := sem.unflushed, trail_end := sem.trail_end, propagated := sem.propagated,
      fuel := sem.fuel, confl_ref := sem.confl_ref, confl_type := sem.confl_type,
      confl_lit0 := sem.confl_lit0, confl_lit1 := sem.confl_lit1, oom := sem.oom,
      vals := sem.vals, flags := sem.flags, lvl := sem.lvl, rsns := sem.rsns,
      trl := sem.trl, trail_pos := sem.trail_pos, wvec := sem.wvec,
      arena := sem.arena, wstk := sem.wstk } = sem := by
  cases s; cases sem
  unfold AgreesExcept fidCoreMask at h
  simp only [FullCoreState.mk.injEq, true_and, and_true] at h
  rcases h with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

theorem fid_exit_hQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (ignore_ref : BitVec 64) (R : Mem 64 → Prop) (Q : Post [i64])
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (r : BitVec 64) (st : FullState) (m' : Mem 64)
    (hag : AgreesExcept fidCoreMask s.core st.core)
    (hscr : FidScr s st)
    (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    (htr : FullPropDecSpecs.FullTrailExt s.core st.core)
    (hperm : FullPropDecSpecs.FullArenaPermEq s.core st.core)
    (hd0 : c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed)
    (hfuel : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hr0 : r = 0#64 → st.core.propagated = st.core.trail_end ∧
      st.core.confl_type = s.core.confl_type ∧ (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur st.core ∧
      (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref))
    (hr2 : r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64)
    (hnoop : s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s)
    (hm : (FullMem c st ⋆ R) m') : Q (r, ()) m' := by
  have hst_eq :
      ({ core := { s.core with
          vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
          rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
          trail_end := st.core.trail_end, propagated := st.core.propagated,
          unassigned := st.core.unassigned, unflushed := st.core.unflushed,
          wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
          confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
          confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
          oom := st.core.oom }
         scratch := { s.scratch with
          search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
          phases := st.scratch.phases, delayed := st.scratch.delayed } } : FullState) = st := by
    cases st; dsimp only; congr 1
    · exact fid_core_eq_of_agrees s.core _ hag
    · exact hscr.symm
  exact hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
    st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
    st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
    st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
    st.scratch.search_ticks st.scratch.wsort st.scratch.phases st.scratch.delayed m'
    (hst_eq.symm ▸ hlen) (hst_eq.symm ▸ hw) (hst_eq.symm ▸ htr) (hst_eq.symm ▸ hperm)
    hd0 hfuel hr hr0
    (fun h1 => by
      obtain ⟨h1a, h1b, h1c, h1d⟩ := hr1 h1
      refine ⟨h1a, h1b, ?_, h1d⟩
      rw [hst_eq]; exact fullConflOkW_to_fullConflictOkW h1c)
    hr2 (fun h => by simpa [hst_eq] using hnoop h)
    (hst_eq.symm ▸ hm)

/-! ## 2. Post-Scan AST Builders (Compaction, Final Flush, Exits) -/

/-- `h->search_ticks += ticks; return brk`. -/
@[expose] def fidPostTicksExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (h_p tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p1 =>
  .load i64 (.var p1.1) fun ld =>
  .let_ (Op.mk (.add i64) (.var ld, (.var tk_b, ()))) fun p2 =>
  .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p3 =>
  .store (.var p2.1) (.var p3.1) (.ret (.var brk_c, ()))

/-- `if (brk != 0) { if (brk == 2) h->oom = 1; h->fuel = fuel; ...; return brk; }`, else continue
with `prop + 1`. -/
@[expose] def fidPostBrkContExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p prop_v fuel1 te_b un_b uf_b tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .ne i64) (.var brk_c, (.imm 0, ()))) fun c0 =>
  .jnz (.var c0.1)
    (.group (sig := [[]])
      (fun _Js_brk => .cons (fun _ =>
        .let_ (Op.mk (.add i64) (.var h_p, (.imm 168, ()))) fun p0 =>
        .store (.var fuel1) (.var p0.1) (
          .let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p1 =>
          .let_ (Op.mk (.add i64) (.var h_p, (.imm 152, ()))) fun p2 =>
          .store (.var p1.1) (.var p2.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p3 =>
            .store (.var te_b) (.var p3.1) (
              .let_ (Op.mk (.add i64) (.var h_p, (.imm 792, ()))) fun p4 =>
              .store (.var un_b) (.var p4.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm 512, ()))) fun p5 =>
                .store (.var uf_b) (.var p5.1)
                  (fidPostTicksExpr h_p tk_b brk_c)))))) .nil)
      (fun Js_brk =>
        .let_ (Op.mk (.cmp .eq i64) (.var brk_c, (.imm 2, ()))) fun c2 =>
        .jnz (.var c2.1)
          (.let_ (Op.mk (.add i64) (.var h_p, (.imm 760, ()))) fun p6 =>
           .store (t := i64) (.imm 1) (.var p6.1) (.jump Js_brk.1 ()))
          (.jump Js_brk.1 ())))
    (.let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p7 =>
     .jump J_out (.var p7.1, (.var te_b, (.var fuel1, (.var un_b, (.var uf_b,
       (.var tk_b, ())))))))

/-- Final delayed-watch flush `if (di > 0) { if (!full_prop_flush_del_fid(h, di)) brk = 2; }`. -/
@[expose] def fidPostFlushExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun _Jfl => .cons (fun brk_f =>
      fidPostBrkContExpr J_out h_p prop_v fuel1 te_b un_b uf_b tk_b brk_f.1) .nil)
    (fun Jfl =>
      .let_ (Op.mk (.cmp .ugt i64) (.var di_b, (.imm 0, ()))) fun cd =>
      .jnz (.var cd.1)
        (.group (sig := [[i64]])
          (fun _Js_5 => .cons (fun r => .jump Jfl.1 (.var r.1, ())) .nil)
          (fun Js_5 =>
            @Expr.call _ _ [i64] "full_prop_flush_del_fid" [i64, i64] [.bool]
              (.var h_p, (.var di_b, ())) fun ok =>
            .jnz (.var ok.1)
              (.jump Js_5.1 (.var brk_b, ()))
              (.jump Js_5.1 (.imm 2, ()))))
        (.jump Jfl.1 (.var brk_b, ())))

/-- Watch compaction tail copy, slice-size store, sentinel fill, then final flush / exit. -/
@[expose] def fidCompactAndPostExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p pWstk pWvec nl64 prop_v fuel1 te_b un_b uf_b tk_b off_b p_b q_b end_b di_b
      brk_b : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun Jc => .cons (fun pc_qc =>
      .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.1, (.var end_b, ()))) fun c_lt =>
      .jnz (.var c_lt.1)
        (.let_ (Op.mk (.mul i64) (.var pc_qc.2.1, (.imm 4, ()))) fun oq =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var oq.1, ()))) fun pq =>
         .let_ (Op.mk (.mul i64) (.var pc_qc.1, (.imm 4, ()))) fun op =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var op.1, ()))) fun pp =>
         .load i32 (.var pp.1) fun ld =>
         .store (.var ld) (.var pq.1) (
           .let_ (Op.mk (.add i64) (.var pc_qc.2.1, (.imm 1, ()))) fun qc1 =>
           .let_ (Op.mk (.add i64) (.var pc_qc.1, (.imm 1, ()))) fun pc1 =>
           .jump Jc.1 (.var pc1.1, (.var qc1.1, ()))))
        (.let_ (Op.mk (.add i64) (.var nl64, (.imm 1, ()))) fun idx1 =>
         .let_ (Op.mk (.mul i64) (.var idx1.1, (.imm 4, ()))) fun off1 =>
         .let_ (Op.mk (.add i64) (.var pWvec, (.var off1.1, ()))) fun ptr1 =>
         .let_ (Op.mk (.sub i64) (.var pc_qc.2.1, (.var off_b, ()))) fun dif =>
         .let_ (Op.mk (.trunc 64 32) (.var dif.1, ())) fun sz32 =>
         .store (.var sz32.1) (.var ptr1.1)
           (.group (sig := [[]])
             (fun _Jfn => .cons (fun _ =>
               fidPostFlushExpr J_out h_p prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b) .nil)
             (fun Jfn =>
               .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.2.1, (.var end_b, ()))) fun ck =>
               .jnz (.var ck.1)
                 (.let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu =>
                  .load i64 (.var pwu.1) fun wu =>
                  .let_ (Op.mk (.sub i64) (.var end_b, (.var pc_qc.2.1, ()))) fun df =>
                  .let_ (Op.mk (.add i64) (.var wu, (.var df.1, ()))) fun wu1 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu2 =>
                  .store (.var wu1.1) (.var pwu2.1)
                    (.group (sig := [[i64]])
                      (fun Jk => .cons (fun k =>
                        .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_b, ()))) fun c_k =>
                        .jnz (.var c_k.1)
                          (.let_ (Op.mk (.mul i64) (.var k.1, (.imm 4, ()))) fun ok =>
                           .let_ (Op.mk (.add i64) (.var pWstk, (.var ok.1, ()))) fun pk =>
                           .store (t := i32) (.imm 0xFFFFFFFF) (.var pk.1) (
                             .let_ (Op.mk (.add i64) (.var k.1, (.imm 1, ()))) fun k1 =>
                             .jump Jk.1 (.var k1.1, ())))
                          (.jump Jfn.1 ())) .nil)
                      (fun Jk => .jump Jk.1 (.var pc_qc.2.1, ()))))
                 (.jump Jfn.1 ()))))) .nil)
    (fun Jc => .jump Jc.1 (.var p_b, (.var q_b, ())))

/-- Post-scan overflow handler: flush pending delayed watches, cold `full_prop_lit_ovf_hot`
push, `wvec[nl64]` slice rebase, then arena swap (pushed) or keep-watch + `brk = 2` (failed). -/
@[expose] def fidPostLpOvfExpr (c : FullCfg) (nl64 : Val i64) (not_lit_v : Val i32)
    (off_o end_o : Val i64)
    (Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (te_p un_p uf_p tk_p p_p q_p di_p brk_p : Val i64) (ovf_p : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64]])
    (fun _Js0 => Blocks.cons
      (fun p1 => Expr.jump Lo
        (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p, Arg.var p1.fst,
          Arg.var p1.snd.fst, Arg.var p1.snd.snd.fst, Arg.var p1.snd.snd.snd.fst,
          Arg.var p1.snd.snd.snd.snd.fst, Arg.var p1.snd.snd.snd.snd.snd.fst, Arg.var ovf_p,
          ()))
      Blocks.nil)
    (fun Js0 =>
      Expr.jnz (Arg.var ovf_p)
        (Expr.group (sig := [[i64, Ty.bool]])
          (fun _Jf => Blocks.cons
            (fun pf =>
              Expr.group (sig := [[Ty.bool]])
                (fun _Jp => Blocks.cons
                  (fun pk =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var nl64, Arg.imm 4, ())⟩ fun boff =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWvec, Arg.var boff.fst, ())⟩
                      fun addr =>
                    Expr.load i32 (Arg.var addr.fst) fun noff32 =>
                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noff32, ())⟩ fun noff =>
                    Expr.group (sig := [[i64, i64, i64, i64]])
                      (fun _Jn => Blocks.cons
                        (fun pn =>
                          Expr.jnz (Arg.var pk.fst)
                            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovf_cr_p, ())⟩ fun cr64 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var cr64.fst, Arg.imm 3, ())⟩
                              fun obase =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var obase.fst, Arg.imm 4, ())⟩ fun b3 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b3.fst, ())⟩
                              fun a3 =>
                            Expr.store (Arg.var ovf_oth_p) (Arg.var a3.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.imm 1, ())⟩
                              fun ob1 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var ob1.fst, Arg.imm 4, ())⟩ fun b4 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b4.fst, ())⟩
                              fun a4 =>
                            Expr.store (Arg.var ovf_rw_p) (Arg.var a4.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.var ovf_ri_p, ())⟩
                              fun obri =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var obri.fst, Arg.imm 4, ())⟩
                              fun bri =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var bri.fst, ())⟩
                              fun ari =>
                            Expr.store (Arg.var not_lit_v) (Arg.var ari.fst) $
                            Expr.jump Js0.fst
                              (Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var pn.snd.snd.fst,
                                Arg.var pn.snd.snd.snd.fst, Arg.var pf.fst, Arg.var brk_p, ()))
                            (Expr.let_ ⟨OpCode.mul i64, (Arg.var pn.snd.snd.fst, Arg.imm 4, ())⟩
                              fun bq =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq.fst, ())⟩
                              fun aq =>
                            Expr.store (Arg.var ovf_oth_p) (Arg.var aq.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 1, ())⟩
                              fun q1 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun bq1 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq1.fst, ())⟩
                              fun aq1 =>
                            Expr.store (Arg.var ovf_cr_p) (Arg.var aq1.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 2, ())⟩
                              fun q2 =>
                            Expr.jump Bo
                              (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p,
                                Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var q2.fst,
                                Arg.var pn.snd.snd.snd.fst, Arg.var pf.fst, Arg.imm 2,
                                Arg.var ovf_p, ())))
                        Blocks.nil)
                      (fun Jn =>
                        Expr.let_ ⟨OpCode.cmp CmpOp.ne i64, (Arg.var noff.fst, Arg.var off_o, ())⟩
                          fun ne =>
                        Expr.jnz (Arg.var ne.fst)
                          (Expr.let_ ⟨OpCode.sub i64, (Arg.var q_p, Arg.var off_o, ())⟩ fun qoff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var qoff.fst, ())⟩
                            fun qn =>
                          Expr.let_ ⟨OpCode.sub i64, (Arg.var p_p, Arg.var off_o, ())⟩ fun poff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var poff.fst, ())⟩
                            fun pn =>
                          Expr.let_ ⟨OpCode.sub i64, (Arg.var end_o, Arg.var off_o, ())⟩ fun eoff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var eoff.fst, ())⟩
                            fun en =>
                          Expr.jump Jn.fst
                            (Arg.var noff.fst, Arg.var pn.fst, Arg.var qn.fst, Arg.var en.fst, ()))
                          (Expr.jump Jn.fst
                            (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, ()))))
                  Blocks.nil)
                (fun Jp =>
                  Expr.jnz (Arg.var pf.snd.fst)
                    (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool])
                      "full_prop_lit_ovf_hot"
                      (Arg.var c.hdr, Arg.var ovf_rw_p, Arg.var ovf_oth_p, Arg.var ovf_cr_p, ())
                      fun pok =>
                    Expr.jump Jp.fst (Arg.var pok.fst, ()))
                    (Expr.jump Jp.fst (Arg.imm false, ()))))
            Blocks.nil)
          (fun Jf =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var di_p, Arg.imm 0, ())⟩ fun cd =>
            Expr.jnz (Arg.var cd.fst)
              (Expr.call (as := [i64, i64]) (bs := [.bool]) "full_prop_flush_del_fid"
                (Arg.var c.hdr, Arg.var di_p, ()) fun fok =>
              Expr.jump Jf.fst (Arg.imm 0, Arg.var fok.fst, ()))
              (Expr.jump Jf.fst (Arg.var di_p, Arg.imm true, ()))))
        (Expr.jump Js0.fst (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o,
          Arg.var di_p, Arg.var brk_p, ())))

/-! ## 3. Exit Lemmas (Normal / Fuel-Exhausted Return, Conflict \& OOM Breaks) -/

theorem fid_outer_flush_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {ignore_ref prop_v tend_v fuel_v unass_v unfl_v ticks' r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hsc_o : FidScr s sem)
    (hd0_o : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hprop_eq : sem.core.propagated = prop_v.toNat)
    (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hfuel_eq : sem.core.fuel = fuel_v)
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
            fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat
            unassigned := unass_v, unflushed := unfl_v }
        scratch := { sem.scratch with search_ticks := ticks' } } ⋆ R) m) :
    Q (r, ()) m := by
  let sem_fin : FullState :=
    { sem with
      core :=
        { sem.core with
          fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat
          unassigned := unass_v, unflushed := unfl_v }
      scratch := { sem.scratch with search_ticks := ticks' } }
  have hfin_core :
      { sem.core with
        fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat
        unassigned := unass_v, unflushed := unfl_v } = sem.core := by
    rw [← hfuel_eq, ← hprop_eq, ← htend_eq, ← hunass_eq, ← hunfl_eq]
  have hlen_fin : sem_fin.LengthsOk c :=
    ⟨by dsimp only [sem_fin]; rw [hfin_core]; exact hlen_o.core_ok,
     by dsimp only [sem_fin]; exact { hlen_o.scratch_ok with }⟩
  have hw_fin : FullWitnessInv c F0 F_cur sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hw_o
  have htr_fin : FullPropDecSpecs.FullTrailExt s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact htr_o
  have hperm_fin : FullPropDecSpecs.FullArenaPermEq s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hperm_o
  have hag_fin : AgreesExcept fidCoreMask s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hag_o
  have hsc_fin : FidScr s sem_fin := by
    unfold FidScr at hsc_o ⊢; dsimp only [sem_fin]; rw [hsc_o]
  exact fid_exit_hQ c F0 F_cur s ignore_ref R Q hQ r sem_fin m
    hag_fin hsc_fin hlen_fin hw_fin htr_fin hperm_fin hd0_o
    (by dsimp only [sem_fin]; rw [← hfuel_eq]; exact hfuel_le) hr
    (fun h => by dsimp only [sem_fin]; rw [← hfuel_eq]; exact hr0 h)
    (fun h => absurd h hr1)
    (fun h => by dsimp only [sem_fin]; rw [← hfuel_eq]; exact hr2 h)
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

theorem fid_post_exit_brk2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v fuel1 ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept fidCoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel1 : fuel1.toNat ≤ s.core.fuel.toNat)
    (hsc_c : FidScr s st_c)
    (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1,
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (2#64, ()) m := by
  let st_fin2 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1
          trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f2 : st_fin2.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin2]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f2 : FullWitnessInv c F0 F_cur st_fin2.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f2.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f2 : WatchesInv F_cur st_fin2.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin2.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin2, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f2
  exact fid_exit_hQ c F0 F_cur s ignore_ref R Q hQ 2#64 st_fin2 m
    (hag_sc.update (fun k =>
      { k with
        oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }))
    (by unfold FidScr at hsc_c ⊢; dsimp only [st_fin2]; rw [hsc_c])
    hlen_f2 hwf_f2
    ⟨by simpa [st_fin2, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c) hd0_c
    hfuel1 (Or.inr (Or.inr rfl))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => Or.inl (by simp [st_fin2]))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

theorem fid_post_exit_brk1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v fuel1 ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept fidCoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_lt : fuel1.toNat < s.core.fuel.toNat)
    (hoom_c : st_c.core.oom = 0#64)
    (hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core)
    (hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref)
    (hsc_c : FidScr s st_c)
    (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
        unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (1#64, ()) m := by
  let st_fin1 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat
          unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f1 : st_fin1.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin1]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f1 : FullWitnessInv c F0 F_cur st_fin1.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f1.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f1 : WatchesInv F_cur st_fin1.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin1.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin1, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f1
  have hconfl_f1 : FullPropDecSpecs.FullConflOkW F_cur st_fin1.core :=
    m7_fullConflOkW_of_perm
      (m7_arenaPermEq_congr rfl rfl rfl rfl (.refl st_c.core))
      rfl rfl rfl rfl rfl rfl hconfl_w
  exact fid_exit_hQ c F0 F_cur s ignore_ref R Q hQ 1#64 st_fin1 m
    (hag_sc.update (fun k =>
      { k with
        fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat
        unassigned := un_b, unflushed := uf_b }))
    (by unfold FidScr at hsc_c ⊢; dsimp only [st_fin1]; rw [hsc_c])
    hlen_f1 hwf_f1
    ⟨by simpa [st_fin1, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c) hd0_c
    (Nat.le_of_lt hfuel_lt)
    (Or.inr (Or.inl rfl))
    (fun h => absurd h (by decide))
    (fun _ => ⟨hfuel_lt, by simp [st_fin1, hoom_c], hconfl_f1,
      fun h2 => by simpa [st_fin1] using hc2_ign h2⟩)
    (fun h => absurd h (by decide))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

/-! ## 4. Post-Compaction Flush \& Exit / Continue -/

theorem fid_post_brk_cont_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b st_c : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b brk_c : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mc0 : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 →
      sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b →
      sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      sem_next.core.confl_type = s.core.confl_type →
      sem_next.core.dense_mode = 0#64 →
      sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level →
      sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated →
      te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc →
      FidScr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (_hsc_o : FidScr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (_hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (_hpi_b_len : sem_b.LengthsOk c)
    (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_c = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_c = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_c = 0#64 ∨ brk_c = 1#64 ∨ brk_c = 2#64)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (hag_l : AgreesExcept propLitCoreMask s_base.core st_c.core)
    (htr_l : FullPropDecSpecs.FullTrailExt s_base.core st_c.core)
    (hperm_l : FullPropDecSpecs.FullArenaPermEq s_base.core st_c.core)
    (hoom_c : st_c.core.oom = sem_b.core.oom)
    (hct_c : st_c.core.confl_type = sem_b.core.confl_type)
    (hcr_c : st_c.core.confl_ref = sem_b.core.confl_ref)
    (hc0_c : st_c.core.confl_lit0 = sem_b.core.confl_lit0)
    (hc1_c : st_c.core.confl_lit1 = sem_b.core.confl_lit1)
    (hcv_c : st_c.core.cur_vars = sem_b.core.cur_vars)
    (hvals_c : st_c.core.vals = sem_b.core.vals)
    (hte_c : st_c.core.trail_end = sem_b.core.trail_end)
    (hun_c : st_c.core.unassigned = sem_b.core.unassigned)
    (huf_c : st_c.core.unflushed = sem_b.core.unflushed)
    (halen_c : st_c.core.arena_len = sem_b.core.arena_len)
    (hcl_c : st_c.core.cur_level = sem_b.core.cur_level)
    (har_c : st_c.core.arena = sem_b.core.arena)
    (hsc_c : FidScr s st_c)
    (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hmc0 : (FullMem c (fastPropMem s_disk st_c) ⋆ R) mc0) :
    wp Γ Q X (fidPostBrkContExpr J_out c.hdr prop_v fuel1 te_b un_b uf_b tk_b brk_c) mc0 := by
  obtain ⟨te_mem, rfl, htem_le, hpr_tem⟩ := hs_disk
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b_tr.te_ge; rw [hs_base] at this; exact this
  have hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat := by
    rw [hte_b]; exact Nat.le_trans hp_lt_o hte_sem_le
  have hfuel1_lt : fuel1.toNat < s.core.fuel.toNat := by
    rw [hfuel1]; exact Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le
  have hag_base : AgreesExcept fidCoreMask s.core s_base.core := by
    unfold AgreesExcept fidCoreMask at hag_o ⊢
    rw [hs_base]; exact hag_o
  have hag_sc : AgreesExcept fidCoreMask s.core st_c.core :=
    hag_base.trans_mono hag_l (fun _ => rfl) (fun _ => rfl)
  have hdm_c : st_c.core.dense_mode = 0#64 :=
    (hag_l.get FullCoreState.dense_mode).trans hdense_b
  have hpr_c : st_c.core.propagated = s.core.propagated := by
    simpa [hs_base] using hag_l.get FullCoreState.propagated
  have hfuel_cs : st_c.core.fuel = s.core.fuel := by
    rw [hag_l.get FullCoreState.fuel, hs_base]
  have hprob_c : st_c.core.probing = s.core.probing := by
    rw [hag_l.get FullCoreState.probing, hs_base]; exact hprob_o
  have htemc_le : te_mem ≤ st_c.core.trail_end := hte_c ▸ Nat.le_trans htem_le hte_sem_le
  let s_dmc : FullState := { s with core := { s.core with trail_end := te_mem } }
  have hsdmc_len : s_dmc.LengthsOk c :=
    ⟨{ hlen0.core_ok with
        trail_end_le := by
          dsimp only [s_dmc]
          rw [← hcv_o, show sem.core.cur_vars = st_c.core.cur_vars from by
            rw [hcv_c, hpi_b_cv, hs_base]]
          exact Nat.le_trans htemc_le hlen_c.core_ok.trail_end_le
        propagated_le := hpr_tem },
     hlen0.scratch_ok⟩
  have hmem_c_len' := fastPropMem_lengthsOk hsdmc_len hlen_c
    (by simpa [s_dmc, hcv_c, hpi_b_cv, hs_base] using hcv_o)
    (by simp [s_dmc, hpr_c]) rfl
  have hte_c_eq : te_b.toNat = st_c.core.trail_end := hte_b.trans hte_c.symm
  have hun_c_eq : un_b = st_c.core.unassigned := hun_b.trans hun_c.symm
  have huf_c_eq : uf_b = st_c.core.unflushed := huf_b.trans huf_c.symm
  have htr_c' : FullPropDecSpecs.FullTrailExt sem.core st_c.core := by
    rw [hs_base] at htr_l; exact ⟨htr_l.te_ge, htr_l.trl_pref, htr_l.lvl_pres⟩
  have htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core := htr_o.trans htr_c'
  have hperm_c' : FullPropDecSpecs.FullArenaPermEq sem.core st_c.core := by
    rw [hs_base] at hperm_l; exact hperm_l
  have hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core := hperm_o.trans hperm_c'
  have hperm_bc : FullPropDecSpecs.FullArenaPermEq sem_b.core st_c.core :=
    m7_arenaPermEq_congr rfl rfl har_c halen_c (.refl sem_b.core)
  unfold fidPostBrkContExpr fidPostTicksExpr
  fid_hsplit
  · have hbrk_ne0 : brk_c ≠ 0#64 := hc
    clear hc
    refine wp_unroll_group fun Js_brk hJs_brk => ?_
    fid_hsplit
    · subst hc
      fid_hsteps
      exact fid_post_exit_brk2 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
        (Nat.le_of_lt hfuel1_lt) hsc_c hd0_c hte_c_eq hpr_lt hpr_lt_teb
        (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
          BitVec.ofNat_eq_ofNat] using hm)
    · have hbrk1 : brk_c = 1#64 := by
        rcases hbr_cases with rfl | rfl | rfl
        · exact absurd rfl hbrk_ne0
        · rfl
        · exact absurd rfl hc
      subst hbrk1
      have ⟨hconfl_c, hoom_b⟩ := hbr1 rfl
      have hoom_c : st_c.core.oom = 0#64 := hoom_c.trans hoom_b
      have hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core := by
        rcases hconfl_c with hne0 | hok
        · exact absurd hoom_b hne0
        · exact m7_fullConflOkW_of_perm hperm_bc hcv_c hvals_c hct_c hcr_c hc0_c hc1_c hok.1
      have hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref := by
        rcases hconfl_c with hne0 | hok
        · exact absurd hoom_b hne0
        · intro h2
          rw [hct_c] at h2
          simpa [hcr_c] using hok.2 h2
      fid_hsteps
      exact fid_post_exit_brk1 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
        hfuel1_lt hoom_c hconfl_w hc2_ign hsc_c hd0_c hte_c_eq hpr_lt hpr_lt_teb
        (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
          BitVec.ofNat_eq_ofNat] using hm)
  · have ⟨hoom_b0, hct_b0⟩ := hbr0 hc
    have hoom_c0 : st_c.core.oom = 0#64 := hoom_c.trans hoom_b0
    have hct_c0 : st_c.core.confl_type = s.core.confl_type := hct_c.trans hct_b0
    fid_hsteps
    let sem_next : FullState :=
      { st_c with core := { st_c.core with propagated := prop_v.toNat + 1, fuel := fuel1 } }
    have hlen_next : sem_next.LengthsOk c :=
      ⟨{ hlen_c.core_ok with propagated_le := by rw [← hte_c_eq]; exact hpr_lt_teb },
       { hlen_c.scratch_ok with }⟩
    have hwf_next : FullWitnessInv c F0 F_cur sem_next.core := by
      have hnw := fullWitnessInv_nw_congr hlen_next.core_ok.cur_vars_le
        (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hwat_next : WatchesInv F_cur sem_next.core := by
        have hw_sp : ModeWatchesInv F_cur sem_next.core :=
          hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        simpa only [ModeWatchesInv, sem_next, hdm_c, ↓reduceIte] using hw_sp
      exact fullWitnessInv_of_nw hnw hdm_c hwat_next
    have hcl_sb : sem_b.core.cur_level = s.core.cur_level := by
      have h1 : st_c.core.cur_level = s_base.core.cur_level :=
        hag_l.get FullCoreState.cur_level
      rw [← hcl_c, h1, hs_base]; exact hcl_o
    have halen_sb : sem_b.core.arena_len = s.core.arena_len := by
      have h1 : st_c.core.arena_len = s_base.core.arena_len :=
        hag_l.get FullCoreState.arena_len
      rw [← halen_c, h1, hs_base]; exact halen_o
    exact hJ_out sem_next te_mem mc0 hlen_next hwf_next
      ⟨by simpa [sem_next] using htr_s_c.te_ge,
       by simpa [sem_next] using htr_s_c.trl_pref,
       by simpa [sem_next] using htr_s_c.lvl_pres⟩
      (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
      (hag_sc.update (fun k => { k with propagated := prop_v.toNat + 1, fuel := fuel1 }))
      (by simp [sem_next, hp1_prop]) rfl hte_c_eq.symm hun_c_eq.symm huf_c_eq.symm
      (by simp [sem_next, hoom_c0]) (by simp [sem_next, hct_c0]) hdm_c
      (by rw [hcv_c, hpi_b_cv, hs_base]; exact hcv_o)
      (by rw [hcl_c]; exact hcl_sb)
      hprob_c
      (by rw [halen_c]; exact halen_sb)
      (by dsimp only [sem_next]; rw [hfuel1]; exact hfl_rem_dec)
      hfuel1_lt (Nat.le_of_lt hfuel1_lt)
      (by simp [sem_next]; omega) htemc_le hpr_tem
      (by unfold FidScr at hsc_c ⊢; exact hsc_c) hd0_c
      (by simpa [sem_next, fastPropMem, hpr_c, hfuel_cs] using hmc0)

/-- Transfer `WatchesInv` across states agreeing on all watch-relevant fields. -/
theorem fid_watches_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : WatchesInv F_cur k) (hdm : k.dense_mode = 0#64) (hdm' : k'.dense_mode = k.dense_mode)
    (hvars : k'.cur_vars = k.cur_vars) (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk)
    (hl : k'.wlen = k.wlen) (ha : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k) :
    WatchesInv F_cur k' := by
  have hm : ModeWatchesInv F_cur k := by simp only [ModeWatchesInv, hdm, ↓reduceIte]; exact h
  have hm' := hm.with_wstk hdm' hvars hw hs hl (fun r hr => ha ▸ hr)
  simpa only [ModeWatchesInv, hdm', hdm, ↓reduceIte] using hm'

/-- Final delayed-watch flush `if (di > 0) { if (!full_prop_flush_del_fid(h, di)) brk = 2; }`
followed by exit / continue. -/
theorem fid_post_flush_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b st_fin : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b : BitVec 64}
    {not_lit : BitVec 32} {dlen_b : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mf : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hQ : FidHQ c F0 F_cur s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 →
      sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b →
      sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      sem_next.core.confl_type = s.core.confl_type →
      sem_next.core.dense_mode = 0#64 →
      sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level →
      sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated →
      te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc →
      FidScr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (_hsc_o : FidScr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hpi_b_len : sem_b.LengthsOk c)
    (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
    (hdi_b : di_b.toNat = 3 * dlen_b) (hdlen_b : dlen_b ≤ c.delayed_cap)
    (hdok_b : DelayedWatchesOk s_base.core st_fin.scratch.delayed dlen_b not_lit.toNat)
    (hlen_f : st_fin.LengthsOk c) (hwf_f : FullWitnessInv c F0 F_cur st_fin.core)
    (hag_f : AgreesExcept propLitCoreMask s_base.core st_fin.core)
    (htr_f : FullPropDecSpecs.FullTrailExt s_base.core st_fin.core)
    (hperm_f : FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core)
    (hoom_f : st_fin.core.oom = sem_b.core.oom)
    (hct_f : st_fin.core.confl_type = sem_b.core.confl_type)
    (hcr_f : st_fin.core.confl_ref = sem_b.core.confl_ref)
    (hc0_f : st_fin.core.confl_lit0 = sem_b.core.confl_lit0)
    (hc1_f : st_fin.core.confl_lit1 = sem_b.core.confl_lit1)
    (hcv_f : st_fin.core.cur_vars = sem_b.core.cur_vars)
    (hvals_f : st_fin.core.vals = sem_b.core.vals)
    (hte_f : st_fin.core.trail_end = sem_b.core.trail_end)
    (hun_f : st_fin.core.unassigned = sem_b.core.unassigned)
    (huf_f : st_fin.core.unflushed = sem_b.core.unflushed)
    (halen_f : st_fin.core.arena_len = sem_b.core.arena_len)
    (hcl_f : st_fin.core.cur_level = sem_b.core.cur_level)
    (har_f : st_fin.core.arena = sem_b.core.arena)
    (hscr_f : FidScr s st_fin)
    (hd0_f : c.delayed_cap = 0 → st_fin.scratch.delayed = s.scratch.delayed)
    (hmf : (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) :
    wp Γ Q X (fidPostFlushExpr J_out c.hdr prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b)
      mf := by
  let P : BitVec 64 → Mem 64 → Prop := fun brk_f mfl =>
    ∃ st_fl : FullState,
      st_fl.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_fl.core ∧
      AgreesExcept propLitCoreMask s_base.core st_fl.core ∧
      FullPropDecSpecs.FullTrailExt s_base.core st_fl.core ∧
      FullPropDecSpecs.FullArenaPermEq s_base.core st_fl.core ∧
      st_fl.core.oom = sem_b.core.oom ∧ st_fl.core.confl_type = sem_b.core.confl_type ∧
      st_fl.core.confl_ref = sem_b.core.confl_ref ∧
      st_fl.core.confl_lit0 = sem_b.core.confl_lit0 ∧
      st_fl.core.confl_lit1 = sem_b.core.confl_lit1 ∧
      st_fl.core.cur_vars = sem_b.core.cur_vars ∧ st_fl.core.vals = sem_b.core.vals ∧
      st_fl.core.trail_end = sem_b.core.trail_end ∧
      st_fl.core.unassigned = sem_b.core.unassigned ∧
      st_fl.core.unflushed = sem_b.core.unflushed ∧
      st_fl.core.arena_len = sem_b.core.arena_len ∧
      st_fl.core.cur_level = sem_b.core.cur_level ∧ st_fl.core.arena = sem_b.core.arena ∧
      FidScr s st_fl ∧ (c.delayed_cap = 0 → st_fl.scratch.delayed = s.scratch.delayed) ∧
      (brk_f = 0#64 → brk_b = 0#64) ∧ (brk_f = 1#64 → brk_b = 1#64) ∧
      (brk_f = 0#64 ∨ brk_f = 1#64 ∨ brk_f = 2#64) ∧
      (FullMem c (fastPropMem s_disk st_fl) ⋆ R) mfl
  have hP_fin : ∀ brk_f, (brk_f = 0#64 → brk_b = 0#64) → (brk_f = 1#64 → brk_b = 1#64) →
      (brk_f = 0#64 ∨ brk_f = 1#64 ∨ brk_f = 2#64) → P brk_f mf := fun brk_f h0 h1 hc =>
    ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f, hcr_f, hc0_f, hc1_f, hcv_f,
      hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f, hscr_f, hd0_f, h0, h1, hc, hmf⟩
  unfold fidPostFlushExpr
  refine wp_join_group (fun (brk_f, ()) mfl => P brk_f mfl) ?_ ?_
  · rintro _ ⟨brk_f, ⟨⟩⟩ mfl ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_l, hct_l, hcr_l,
      hc0_l, hc1_l, hcv_l, hvals_l, hte_l, hun_l, huf_l, halen_l, hcl_l, har_l, hscr_l, hd0_l,
      hb0, hb1, hbc, hmfl⟩
    exact fid_post_brk_cont_wp hQ hJ_out hlen0 hpr_lt hs_base hfuel1 hs_disk htr_o
      hperm_o hag_o hcv_o hcl_o hprob_o halen_o _hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o
      hpr_ge hpi_b_len hpi_b_cv hpi_b_tr hdense_b hte_b hun_b huf_b
      (fun h => hbr0 (hb0 h)) (fun h => hbr1 (hb1 h)) hbc hlen_l hwf_l hag_l htr_l hperm_l
      hoom_l hct_l hcr_l hc0_l hc1_l hcv_l hvals_l hte_l hun_l huf_l halen_l hcl_l har_l
      hscr_l hd0_l hmfl
  · intro Jfl hJfl
    fid_hsplit
    · refine wp_join_group (fun (r, ()) m5 => P r m5) ?_ ?_
      · rintro _ ⟨r, ⟨⟩⟩ m5 h5
        fid_hsteps
        exact hJfl (r, ()) m5 h5
      · intro J5 hJ5
        obtain ⟨te_mem, hsd_eq, htem_le, hpr_tem⟩ := hs_disk
        have hdm_f : st_fin.core.dense_mode = 0#64 :=
          (hag_f.get FullCoreState.dense_mode).trans hdense_b
        have hcv_fb : st_fin.core.cur_vars = s_base.core.cur_vars :=
          hag_f.get FullCoreState.cur_vars
        have hsd_len : s_disk.LengthsOk c := by
          rw [hsd_eq]
          exact ⟨{ hlen0.core_ok with
            trail_end_le := by
              have h1 := hpi_b_tr.te_ge
              have h2 := hlen_f.core_ok.trail_end_le
              rw [hs_base] at h1
              rw [hcv_fb, hs_base] at h2
              dsimp only at h1 h2 ⊢
              rw [← hcv_o]; omega
            propagated_le := hpr_tem }, hlen0.scratch_ok⟩
        have hlen_mem : (fastPropMem s_disk st_fin).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hlen_f
            (by rw [hsd_eq, hcv_fb, hs_base]; exact hcv_o)
            (by rw [hsd_eq, hag_f.get FullCoreState.propagated, hs_base]) rfl
        have hwat_f : WatchesInv F_cur st_fin.core := by
          have hw_sp := hwf_f.watches
          simpa only [ModeWatchesInv, hdm_f, ↓reduceIte] using hw_sp
        have hlay_mem : WatchStackLayout (fastPropMem s_disk st_fin).core :=
          fastPropMem_watchLayout hwat_f.layout rfl
        have hdok_mem : DelayedWatchesOk (fastPropMem s_disk st_fin).core
            (fastPropMem s_disk st_fin).scratch.delayed dlen_b not_lit.toNat := by
          rw [fastPropMem_delayed]
          exact delayedWatchesOk_congr (k1 := s_base.core)
            (by rw [fastPropMem_def]; exact hcv_fb)
            (by rw [fastPropMem_def]; exact hperm_f.1) hdok_b
        c0_call hFlush
        refine ⟨c, F_cur, fastPropMem s_disk st_fin, R, dlen_b, not_lit.toNat, rfl, hlen_mem,
          hlay_mem, hdi_b, hdlen_b, hdok_mem, hmf,
          fun ok wv' ws' wl' wu' wso' m' hlen' hlay' hwat' _hsw' hm' => ?_⟩
        let st_fl : FullState :=
          { st_fin with
            core := { st_fin.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
            scratch := { st_fin.scratch with wsort := wso' } }
        have hlen_l : st_fl.LengthsOk c := by
          simp only [fastPropMem_def] at hlen'
          have hso := hlen'.scratch_ok
          have hscr4 : st_fl.scratch.LengthsOk c :=
            ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8,
             hso.9, hso.10, hso.11, hso.12, hso.13, hso.14, hso.15, hso.16,
             hso.17, hso.18, hso.19, hso.20, hso.21, hso.22, hso.23, hso.24⟩
          exact ⟨{ hlen'.core_ok with
              trail_end_le := hlen_f.core_ok.trail_end_le
              propagated_le := hlen_f.core_ok.propagated_le }, hscr4⟩
        have hwat_mem : WatchesInv F_cur (fastPropMem s_disk st_fin).core :=
          fid_watches_congr hwat_f hdm_f (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hwat_l : WatchesInv F_cur st_fl.core :=
          fid_watches_congr (hwat' hwat_mem) (by rw [fastPropMem_def]; exact hdm_f)
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hnw_l : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_fl.core) :=
          fullWitnessInv_nw_congr hlen_l.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen_f.core_ok.cur_vars_le hwf_f)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hwf_l : FullWitnessInv c F0 F_cur st_fl.core :=
          fullWitnessInv_of_nw hnw_l hdm_f hwat_l
        have hm_l : (FullMem c (fastPropMem s_disk st_fl) ⋆ R) m' := by
          simpa only [st_fl, fastPropMem_def] using hm'
        have hscr_l : FidScr s st_fl := by
          unfold FidScr at hscr_f ⊢; dsimp only [st_fl]; rw [hscr_f]
        have hag_l : AgreesExcept propLitCoreMask s_base.core st_fl.core :=
          hag_f.update (fun k => { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
        have htr_l : FullPropDecSpecs.FullTrailExt s_base.core st_fl.core :=
          ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩
        have hperm_l : FullPropDecSpecs.FullArenaPermEq s_base.core st_fl.core :=
          m7_arenaPermEq_congr rfl rfl rfl rfl hperm_f
        fid_hsplit
        · fid_hsteps
          exact hJ5 (brk_b, ()) m' ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f,
            hscr_l, hd0_f, id, id, hbr_cases, hm_l⟩
        · fid_hsteps
          exact hJ5 (2#64, ()) m' ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f,
            hscr_l, hd0_f, fun h => absurd h (by decide), fun h => absurd h (by decide),
            Or.inr (Or.inr rfl), hm_l⟩
    · fid_hsteps
      exact hJfl (brk_b, ()) mf (hP_fin brk_b id id hbr_cases)

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
