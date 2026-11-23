/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1a

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 1c (Compact + Post-Ovf Exit Helpers)

Zero `import all`, plain `public section` (`0` `@[expose]`).
Factors watch compaction, sentinel tail zeroing, chrono check, and outer exit/continue
out of `full_propagate_ignore_hot_wp` so every theorem stays well under heartbeat limits.
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

local macro "m7c_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "m7c_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "m7c_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

theorem m7_shl1_eq_of_trl {trl trl0 : List (BitVec 32)} {i : Nat} {lit : BitVec 32}
    (htrl : trl = trl0) (pf : i < trl.length) (pf0 : i < trl0.length) (h : trl0[i]'pf0 = lit) :
    (BitVec.setWidth 64 (trl[i]'pf ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat =
      2 * (lit ^^^ 1#32).toNat := by
  subst htrl; rw [fc_getElem_eq_of_idx rfl pf pf0, h]
  simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_u32_nat (lit ^^^ 1#32)

theorem m7_shl1_add1_eq_of_trl {trl trl0 : List (BitVec 32)} {i : Nat} {lit : BitVec 32}
    (htrl : trl = trl0) (pf : i < trl.length) (pf0 : i < trl0.length) (h : trl0[i]'pf0 = lit) :
    ((BitVec.setWidth 64 (trl[i]'pf ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
      (1 : BitVec 64)).toNat =
      2 * (lit ^^^ 1#32).toNat + 1 := by
  subst htrl; rw [fc_getElem_eq_of_idx rfl pf pf0, h]
  simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_add1_nat (lit ^^^ 1#32)

theorem m7_arenaPermEq_congr {a b a' b' : FullCoreState}
    (ha : a'.arena = a.arena) (hl : a'.arena_len = a.arena_len)
    (hb : b'.arena = b.arena) (hlb : b'.arena_len = b.arena_len)
    (h : FullPropDecSpecs.FullArenaPermEq a b) : FullPropDecSpecs.FullArenaPermEq a' b' := by
  have hr : fullArenaClauseRefsCore a' = fullArenaClauseRefsCore a := by
    simp only [fullArenaClauseRefsCore, ha, hl]
  have hr' : fullArenaClauseRefsCore b' = fullArenaClauseRefsCore b := by
    simp only [fullArenaClauseRefsCore, hb, hlb]
  have hs : ∀ r, fullArenaClauseSizeCore a' r = fullArenaClauseSizeCore a r := fun r => by
    simp only [fullArenaClauseSizeCore, ha]
  have hs' : ∀ r, fullArenaClauseSizeCore b' r = fullArenaClauseSizeCore b r := fun r => by
    simp only [fullArenaClauseSizeCore, hb]
  have hg : ∀ r, fullArenaClauseGarbCore a' r = fullArenaClauseGarbCore a r := fun r => by
    simp only [fullArenaClauseGarbCore, fullArenaHdrCore, ha]
  have hg' : ∀ r, fullArenaClauseGarbCore b' r = fullArenaClauseGarbCore b r := fun r => by
    simp only [fullArenaClauseGarbCore, fullArenaHdrCore, hb]
  have hl_ : ∀ r, fullArenaClauseLitsCore a' r = fullArenaClauseLitsCore a r := fun r => by
    simp only [fullArenaClauseLitsCore, hs r, ha]
  have hl_' : ∀ r, fullArenaClauseLitsCore b' r = fullArenaClauseLitsCore b r := fun r => by
    simp only [fullArenaClauseLitsCore, hs' r, hb]
  refine ⟨hr'.trans (h.1.trans hr.symm), fun r hrm => ?_⟩
  rw [hr] at hrm
  obtain ⟨h1, h2, h3⟩ := h.2 r hrm
  exact ⟨(hs' r).trans (h1.trans (hs r).symm), (hg' r).trans (h2.trans (hg r).symm),
    by simpa only [hl_' r, hl_ r] using h3⟩

def m7CoreMask (t : FullCoreState) : FullCoreState :=
  { t with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    trail_end := 0, propagated := 0, unassigned := 0#64, unflushed := 0#64,
    wvec := [], arena := [], wstk := [], wlen := 0, wusable := 0#64, fuel := 0#64,
    confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64,
    oom := 0#64 }

theorem m7_agrees_upd_prop_fuel {a b : FullCoreState} {p : Nat} {f : BitVec 64}
    (h : AgreesExcept m7CoreMask a b) :
    AgreesExcept m7CoreMask a { b with propagated := p, fuel := f } := by
  simpa only [AgreesExcept, m7CoreMask] using h

private theorem m7_scratch_trans {s0 s1 s2 : FullState}
    (hbc : s1.scratch = { s0.scratch with
      search_ticks := s1.scratch.search_ticks, wsort := s1.scratch.wsort,
      phases := s1.scratch.phases })
    (hcb : s2.scratch = { s1.scratch with
      search_ticks := s2.scratch.search_ticks, wsort := s2.scratch.wsort,
      phases := s2.scratch.phases }) :
    s2.scratch = { s0.scratch with
      search_ticks := s2.scratch.search_ticks, wsort := s2.scratch.wsort,
      phases := s2.scratch.phases } := by
  rw [hcb, hbc]

theorem m7_core_eq_of_agrees (s sem : FullCoreState)
    (h : AgreesExcept m7CoreMask s sem) :
    { s with
      unassigned := sem.unassigned, wlen := sem.wlen, wusable := sem.wusable,
      unflushed := sem.unflushed, trail_end := sem.trail_end, propagated := sem.propagated,
      fuel := sem.fuel, confl_ref := sem.confl_ref, confl_type := sem.confl_type,
      confl_lit0 := sem.confl_lit0, confl_lit1 := sem.confl_lit1, oom := sem.oom,
      vals := sem.vals, flags := sem.flags, lvl := sem.lvl, rsns := sem.rsns,
      trl := sem.trl, trail_pos := sem.trail_pos, wvec := sem.wvec,
      arena := sem.arena, wstk := sem.wstk } = sem := by
  cases s; cases sem
  simp only [AgreesExcept, m7CoreMask, FullCoreState.mk.injEq] at h
  simp_all

theorem m7_exit_hQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (ignore_ref : BitVec 64) (R : Mem 64 → Prop) (Q : Post [i64])
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unas', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
            confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (r : BitVec 64) (st : FullState) (m' : Mem 64)
    (hag : AgreesExcept m7CoreMask s.core st.core)
    (hscr : st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases })
    (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    (htr : FullPropDecSpecs.FullTrailExt s.core st.core)
    (hperm : FullPropDecSpecs.FullArenaPermEq s.core st.core)
    (hfuel : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hr0 : r = 0#64 → st.core.propagated = st.core.trail_end ∧
      st.core.confl_type = s.core.confl_type ∧ (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur st.core ∧
      (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref) ∧
      (st.core.cur_level = 0 → F0.Unsat))
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
          phases := st.scratch.phases } } : FullState) = st := by
    cases st
    dsimp only
    congr 1
    · exact m7_core_eq_of_agrees s.core _ hag
    · exact hscr.symm
  exact hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
    st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
    st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
    st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
    st.scratch.search_ticks st.scratch.wsort st.scratch.phases m'
    (hst_eq.symm ▸ hlen) (hst_eq.symm ▸ hw) (hst_eq.symm ▸ htr) (hst_eq.symm ▸ hperm)
    hfuel hr hr0 (hst_eq.symm ▸ hr1) hr2 (fun h => by simpa [hst_eq] using hnoop h)
    (hst_eq.symm ▸ hm)

@[expose] def m7PostOvfTicksExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (h_p tk_b : Val i64) (brk_c : Val i64) (rec_ph : Val .bool) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _Js => .cons (fun _ => .ret (.var brk_c, ())) .nil)
    (fun Js =>
      .jnz (.var rec_ph)
        (.let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p1 =>
         .load i64 (.var p1.1) fun ld =>
         .let_ (Op.mk (.add i64) (.var ld, (.var tk_b, ()))) fun p2 =>
         .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p3 =>
         .store (.var p2.1) (.var p3.1) (.jump Js.1 ()))
        (.jump Js.1 ()))

@[expose] def m7PostOvfBrkContExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p prop_v te_b un_b uf_b tk_b : Val i64) (rec_ph : Val .bool)
    (brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .ne i64) (.var brk_c, (.imm 0, ()))) fun c0 =>
  .jnz (.var c0.1)
    (.group (sig := [[]])
      (fun Js_brk => .cons (fun _ =>
        .let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p1 =>
        .let_ (Op.mk (.add i64) (.var h_p, (.imm 152, ()))) fun p2 =>
        .store (.var p1.1) (.var p2.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p3 =>
          .store (.var te_b) (.var p3.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm 792, ()))) fun p4 =>
            .store (.var un_b) (.var p4.1) (
              .let_ (Op.mk (.add i64) (.var h_p, (.imm 512, ()))) fun p5 =>
              .store (.var uf_b) (.var p5.1)
                (m7PostOvfTicksExpr h_p tk_b brk_c rec_ph))))) .nil)
      (fun Js_brk =>
        .let_ (Op.mk (.cmp .eq i64) (.var brk_c, (.imm 2, ()))) fun c2 =>
        .jnz (.var c2.1)
          (.let_ (Op.mk (.add i64) (.var h_p, (.imm 760, ()))) fun p6 =>
           .store (t := i64) (.imm 1) (.var p6.1) (.jump Js_brk.1 ()))
          (.jump Js_brk.1 ())))
    (.let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p7 =>
     .jump J_out (.var p7.1, (.var te_b, (.var un_b, (.var uf_b, (.var tk_b, ()))))))

@[expose] def m7PostOvfBrkExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p prop_v te_b un_b uf_b tk_b brk_b t0_v : Val i64)
    (rec_ph : Val .bool) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun Jch => .cons (fun brk_c =>
      m7PostOvfBrkContExpr J_out h_p prop_v te_b un_b uf_b tk_b rec_ph brk_c.1) .nil)
    (fun Jch =>
      .let_ (Op.mk (.cmp .ne i64) (.var brk_b, (.imm 2, ()))) fun c1 =>
      .jnz (.var c1.1)
        (.let_ (Op.mk (.cmp .ult i64) (.var t0_v, (.var te_b, ()))) fun c2 =>
         .jnz (.var c2.1)
           (.let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p1 =>
            .store (.var te_b) (.var p1.1)
              (.group (sig := [[i64]])
                (fun Js_1 => .cons (fun r => .jump Jch.1 (.var r.1, ())) .nil)
                (fun Js_1 =>
                  @Expr.call _ _ [i64] "full_prop_chrono_hot" [i64, i64] [.bool]
                    (.var h_p, (.var t0_v, ())) fun ok =>
                  .jnz (.var ok.1)
                    (.jump Js_1.1 (.var brk_b, ()))
                    (.jump Js_1.1 (.imm 2, ())))))
           (.jump Jch.1 (.var brk_b, ())))
        (.jump Jch.1 (.var brk_b, ())))

@[expose] def m7CompactAndPostOvfExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p pWstk prop_v te_b un_b uf_b tk_b off_b p_b q_b end_b brk_b t0_v : Val i64)
    (not_lit : Val i32) (rec_ph : Val .bool) : Expr Val Cont [i64] :=
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
        (.let_ (Op.mk (.add i64) (.var h_p, (.imm 104, ()))) fun pwv =>
         .load i64 (.var pwv.1) fun ld_wv =>
         .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun nl64 =>
         .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh1 =>
         .let_ (Op.mk (.shl i64) (.var nl64.1, (.var sh1.1, ()))) fun shl =>
         .let_ (Op.mk (.add i64) (.var shl.1, (.imm 1, ()))) fun idx1 =>
         .let_ (Op.mk (.mul i64) (.var idx1.1, (.imm 4, ()))) fun off1 =>
         .let_ (Op.mk (.add i64) (.var ld_wv, (.var off1.1, ()))) fun ptr1 =>
         .let_ (Op.mk (.sub i64) (.var pc_qc.2.1, (.var off_b, ()))) fun dif =>
         .let_ (Op.mk (.trunc 64 32) (.var dif.1, ())) fun sz32 =>
         .store (.var sz32.1) (.var ptr1.1)
           (.group (sig := [[]])
             (fun Jfn => .cons (fun _ =>
               m7PostOvfBrkExpr J_out h_p prop_v te_b un_b uf_b tk_b brk_b t0_v rec_ph) .nil)
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

private theorem m7_post_ovf_exit_brk2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unas', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
            confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept m7CoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_c : st_c.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hsc_c : st_c.scratch = { s.scratch with
      search_ticks := st_c.scratch.search_ticks,
      wsort := st_c.scratch.wsort, phases := st_c.scratch.phases })
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        oom := 1#64, propagated := prop_v.toNat + 1,
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (2#64, ()) m := by
  let st_fin2 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          oom := 1#64, propagated := prop_v.toNat + 1
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
  exact m7_exit_hQ c F0 F_cur s ignore_ref R Q hQ 2#64 st_fin2 m
    (hag_sc.update (fun k =>
      { k with
        oom := 1#64, propagated := prop_v.toNat + 1
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }))
    (by dsimp only [st_fin2]; rw [hsc_c])
    hlen_f2 hwf_f2
    ⟨by simpa [st_fin2, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
    (by simp [st_fin2, hfuel_c])
    (Or.inr (Or.inr rfl))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => Or.inl (by simp [st_fin2]))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private theorem m7_post_ovf_exit_brk1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unas', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
            confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept m7CoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_lt : st_c.core.fuel.toNat < s.core.fuel.toNat)
    (hoom_c : st_c.core.oom = 0#64)
    (hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core)
    (hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref)
    (hsc_c : st_c.scratch = { s.scratch with
      search_ticks := st_c.scratch.search_ticks,
      wsort := st_c.scratch.wsort, phases := st_c.scratch.phases })
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
        unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (1#64, ()) m := by
  let st_fin1 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          propagated := prop_v.toNat + 1, trail_end := te_b.toNat
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
  exact m7_exit_hQ c F0 F_cur s ignore_ref R Q hQ 1#64 st_fin1 m
    (hag_sc.update (fun k =>
      { k with
        propagated := prop_v.toNat + 1, trail_end := te_b.toNat
        unassigned := un_b, unflushed := uf_b }))
    (by dsimp only [st_fin1]; rw [hsc_c])
    hlen_f1 hwf_f1
    ⟨by simpa [st_fin1, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
    (by simp [st_fin1]; exact Nat.le_of_lt hfuel_lt)
    (Or.inr (Or.inl rfl))
    (fun h => absurd h (by decide))
    (fun _ => ⟨by simp [st_fin1, hfuel_lt], by simp [st_fin1, hoom_c], hconfl_f1,
      fun h2 => by simpa [st_fin1] using hc2_ign h2,
      fun h0 => FullWitnessInv.level0_unsat_of_conflOkW hwf_f1 h0 hconfl_f1⟩)
    (fun h => absurd h (by decide))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private theorem m7_post_ovf_brk_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b st_fin : FullState}
    {ignore_ref prop_v te_b un_b uf_b tk_b brk_b t0_v : BitVec 64}
    {rec_ph : Bool} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mf : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64]}
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unas', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
            confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept m7CoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
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
      sem_next.scratch = { s.scratch with
        search_ticks := sem_next.scratch.search_ticks,
        wsort := sem_next.scratch.wsort, phases := sem_next.scratch.phases } →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core := { sem_next.core with propagated := s.core.propagated } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var un_b, (.var uf_b,
        (.var tk_b, ())))))) mc0)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7CoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (_hpi_b_len : sem_b.LengthsOk c)
    (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hpi_b_sc : sem_b.scratch = { s_base.scratch with
      search_ticks := sem_b.scratch.search_ticks,
      wsort := sem_b.scratch.wsort, phases := sem_b.scratch.phases })
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
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
    (hscr_f : st_fin.scratch = sem_b.scratch)
    (hmf : (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) :
    wp Γ Q X (m7PostOvfBrkExpr J_out c.hdr prop_v te_b un_b uf_b tk_b brk_b t0_v rec_ph) mf := by
  obtain ⟨te_mem, rfl, htem_le, hpr_tem⟩ := hs_disk
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b_tr.te_ge; rw [hs_base] at this; exact this
  have hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat := by
    rw [hte_b]; exact Nat.le_trans hp_lt_o hte_sem_le
  unfold m7PostOvfBrkExpr m7PostOvfBrkContExpr m7PostOvfTicksExpr
  refine wp_join_group (fun (brk_c, ()) mc0 =>
      ∃ st_c : FullState,
        st_c.LengthsOk c ∧
        FullWitnessInv c F0 F_cur st_c.core ∧
        FullPropDecSpecs.FullTrailExt s_base.core st_c.core ∧
        FullPropDecSpecs.FullArenaPermEq s_base.core st_c.core ∧
        AgreesExcept m7CoreMask s.core st_c.core ∧
        st_c.core.cur_vars = sem_b.core.cur_vars ∧
        st_c.core.vals = sem_b.core.vals ∧
        st_c.core.trail_end = sem_b.core.trail_end ∧
        st_c.core.unassigned = sem_b.core.unassigned ∧
        st_c.core.unflushed = sem_b.core.unflushed ∧
        st_c.core.arena_len = sem_b.core.arena_len ∧
        st_c.core.cur_level = sem_b.core.cur_level ∧
        st_c.core.confl_ref = st_fin.core.confl_ref ∧
        st_c.core.confl_lit0 = st_fin.core.confl_lit0 ∧
        st_c.core.confl_lit1 = st_fin.core.confl_lit1 ∧
        (brk_c = 0#64 → st_c.core.oom = 0#64 ∧ st_c.core.confl_type = s.core.confl_type) ∧
        (brk_c = 1#64 → PropLitConfl F_cur ignore_ref st_c.core ∧ st_c.core.oom = 0#64) ∧
        (brk_c = 2#64 → True) ∧
        (brk_c = 0#64 ∨ brk_c = 1#64 ∨ brk_c = 2#64) ∧
        st_c.core.propagated = s.core.propagated ∧
        st_c.core.fuel = s_base.core.fuel ∧
        st_c.core.probing = s.core.probing ∧
        st_c.core.dense_mode = 0#64 ∧
        st_c.scratch = { s.scratch with
          search_ticks := st_c.scratch.search_ticks,
          wsort := st_c.scratch.wsort, phases := st_c.scratch.phases } ∧
        ∃ te_mc : Nat,
          te_mc ≤ st_c.core.trail_end ∧ s.core.propagated ≤ te_mc ∧
          (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } } st_c) ⋆
            R) mc0) ?_ ?_
  · rintro _ ⟨brk_c, ⟨⟩⟩ mc0 ⟨st_c, hlen_c, hwf_c, htr_c, hperm_c, hag_sc, hcv_c,
        hvals_c, hte_c, hun_c, huf_c, halen_c, hcl_c, _hcr_c, _hc0_c, _hc1_c,
        hc_br0, hc_br1, _hc_br2, hc_cases, hpr_c, hfuel_c, hprob_c, hdm_c,
        hsc_c, te_mc, htemc_le, hpr_temc, hmc0⟩
    let s_dmc : FullState := { s with core := { s.core with trail_end := te_mc } }
    have hsdmc_len : s_dmc.LengthsOk c :=
      ⟨{ hlen0.core_ok with
          trail_end_le := by
            dsimp only [s_dmc]
            rw [← hcv_o, show sem.core.cur_vars = st_c.core.cur_vars from by
              rw [hcv_c, hpi_b_cv, hs_base]]
            exact Nat.le_trans htemc_le hlen_c.core_ok.trail_end_le
          propagated_le := hpr_temc },
       hlen0.scratch_ok⟩
    have hmem_c_len' := fastPropMem_lengthsOk hsdmc_len hlen_c
      (by simpa [s_dmc, hcv_c, hpi_b_cv, hs_base] using hcv_o)
      (by simp [s_dmc, hpr_c]) rfl
    have hte_c_eq : te_b.toNat = st_c.core.trail_end := hte_b.trans hte_c.symm
    have hun_c_eq : un_b = st_c.core.unassigned := hun_b.trans hun_c.symm
    have huf_c_eq : uf_b = st_c.core.unflushed := huf_b.trans huf_c.symm
    have htr_c' : FullPropDecSpecs.FullTrailExt sem.core st_c.core := by
      rw [hs_base] at htr_c; exact ⟨htr_c.te_ge, htr_c.trl_pref, htr_c.lvl_pres⟩
    have htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core := htr_o.trans htr_c'
    have hperm_c' : FullPropDecSpecs.FullArenaPermEq sem.core st_c.core := by
      rw [hs_base] at hperm_c; exact hperm_c
    have hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core := hperm_o.trans hperm_c'
    have hfuel_nx_dec : st_c.core.fuel.toNat < s.core.fuel.toNat := by
      rw [hfuel_c, hs_base]
      exact Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le
    m7c_hsplit
    · have hbrk_ne0 : brk_c ≠ 0#64 := hc
      clear hc
      refine wp_unroll_group fun Js_brk hJs_brk => ?_
      m7c_hsplit
      · subst hc
        m7c_hsteps
        · exact m7_post_ovf_exit_brk2 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
            (Nat.le_of_lt hfuel_nx_dec) hsc_c hte_c_eq hpr_lt hpr_lt_teb
            (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
              BitVec.ofNat_eq_ofNat] using hm)
        · exact m7_post_ovf_exit_brk2 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
            (Nat.le_of_lt hfuel_nx_dec) hsc_c hte_c_eq hpr_lt hpr_lt_teb
            (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
              BitVec.ofNat_eq_ofNat] using hm)
      · have hbrk1 : brk_c = 1#64 := by
          rcases hc_cases with rfl | rfl | rfl
          · exact absurd rfl hbrk_ne0
          · rfl
          · exact absurd rfl hc
        subst hbrk1
        have ⟨hconfl_c, hoom_c⟩ := hc_br1 rfl
        have hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core := by
          rcases hconfl_c with hne0 | hok
          · exact absurd hoom_c hne0
          · exact hok.1
        have hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref := by
          rcases hconfl_c with hne0 | hok
          · exact absurd hoom_c hne0
          · exact hok.2
        m7c_hsteps
        · exact m7_post_ovf_exit_brk1 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
            hfuel_nx_dec hoom_c hconfl_w hc2_ign hsc_c hte_c_eq hpr_lt hpr_lt_teb
            (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
              BitVec.ofNat_eq_ofNat] using hm)
        · exact m7_post_ovf_exit_brk1 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
            hfuel_nx_dec hoom_c hconfl_w hc2_ign hsc_c hte_c_eq hpr_lt hpr_lt_teb
            (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
              BitVec.ofNat_eq_ofNat] using hm)
    · have ⟨hoom_c0, hct_c0⟩ := hc_br0 hc
      m7c_hsteps
      let sem_next : FullState :=
        { st_c with core := { st_c.core with propagated := prop_v.toNat + 1 } }
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
        have h1 : st_fin.core.cur_level = s_base.core.cur_level :=
          hag_f.get FullCoreState.cur_level
        rw [← hcl_f, h1, hs_base]; exact hcl_o
      have halen_sb : sem_b.core.arena_len = s.core.arena_len := by
        have h1 : st_fin.core.arena_len = s_base.core.arena_len :=
          hag_f.get FullCoreState.arena_len
        rw [← halen_f, h1, hs_base]; exact halen_o
      exact hJ_out sem_next te_mc mc0 hlen_next hwf_next
        ⟨by simpa [sem_next] using htr_s_c.te_ge,
         by simpa [sem_next] using htr_s_c.trl_pref,
         by simpa [sem_next] using htr_s_c.lvl_pres⟩
        (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
        (hag_sc.update (fun k => { k with propagated := prop_v.toNat + 1 }))
        (by simp [sem_next, hp1_prop]) hte_c_eq.symm hun_c_eq.symm huf_c_eq.symm
        (by simp [sem_next, hoom_c0]) (by simp [sem_next, hct_c0]) hdm_c
        (by rw [hcv_c, hpi_b_cv, hs_base]; exact hcv_o)
        (by rw [hcl_c]; exact hcl_sb)
        hprob_c
        (by rw [halen_c]; exact halen_sb)
        (by dsimp only [sem_next]; rw [hfuel_c, hs_base]; exact hfl_rem_dec)
        hfuel_nx_dec (Nat.le_of_lt hfuel_nx_dec)
        (by simp [sem_next]; omega) htemc_le hpr_temc hsc_c
        (by simpa [sem_next, fastPropMem, hpr_c] using hmc0)
  · intro Jch hJch
    have hag_base : AgreesExcept m7CoreMask s.core s_base.core := by
      simpa only [AgreesExcept, m7CoreMask, hs_base] using hag_o
    have hag_s_fin : AgreesExcept m7CoreMask s.core st_fin.core :=
      hag_base.trans_mono hag_f (fun _ => rfl) (fun _ => rfl)
    m7c_hsplit
    · have hbrk_ne2 : brk_b ≠ 2#64 := hc
      clear hc
      m7c_hsplit
      · have ht0_lt_te : t0_v.toNat < sem_b.core.trail_end := by rw [← hte_b]; exact hc
        have ht0_le_fin : t0_v.toNat ≤ st_fin.core.trail_end := by
          rw [hte_f]; exact Nat.le_of_lt ht0_lt_te
        m7c_hsteps
        let st_c_in : FullState :=
          { st_fin with
            core :=
              { st_fin.core with
                unassigned := s.core.unassigned, unflushed := s.core.unflushed }
            scratch := { st_fin.scratch with search_ticks := s.scratch.search_ticks } }
        have hcin_len : st_c_in.LengthsOk c :=
          ⟨{ hlen_f.core_ok with }, { hlen_f.scratch_ok with }⟩
        have hcin_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_c_in.core) :=
          fullWitnessInv_nw_congr hcin_len.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen_f.core_ok.cur_vars_le hwf_f)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hdm_cin : st_c_in.core.dense_mode = 0#64 :=
          (hag_f.get FullCoreState.dense_mode).trans hdense_b
        have hwat_cin : WatchesInv F_cur st_c_in.core := by
          have hw_sp : ModeWatchesInv F_cur st_c_in.core :=
            hwf_f.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          simpa only [ModeWatchesInv, hdm_cin, ↓reduceIte] using hw_sp
        have hcin_wf : FullWitnessInv c F0 F_cur st_c_in.core :=
          fullWitnessInv_of_nw hcin_nw hdm_cin hwat_cin
        have hpr_f : st_fin.core.propagated = s.core.propagated := by
          have := hag_f.get FullCoreState.propagated
          rw [this, hs_base]
        have hm_cin : (FullMem c st_c_in ⋆ R) m := by
          simpa only [st_c_in, fastPropMem, hte_f, hte_b, hpr_f] using hm
        c0_call hChrono
        refine ⟨c, F0, F_cur, st_c_in, R, rfl, hcin_len, hcin_wf,
          hdm_cin, by simpa [st_c_in] using ht0_le_fin, hm_cin,
          fun ok wv' ar' ws' wl' wu' oom' wso' mc' hlen' hwf' hperm' hok_t
            hok_f hmc' => ?_⟩
        let st_c' : FullState :=
          { st_fin with
            core :=
              { st_fin.core with
                wvec := wv', arena := ar', wstk := ws', wlen := wl',
                wusable := wu', oom := oom' }
            scratch := { st_fin.scratch with wsort := wso' } }
        have hlen_c' : st_c'.LengthsOk c :=
          ⟨{ hlen'.core_ok with }, { hlen'.scratch_ok with }⟩
        have hnw_c' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_c'.core) :=
          fullWitnessInv_nw_congr hlen_c'.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen'.core_ok.cur_vars_le hwf')
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hdm_c' : st_c'.core.dense_mode = 0#64 := hdm_cin
        have hwat_c' : WatchesInv F_cur st_c'.core := by
          have hw_sp : ModeWatchesInv F_cur st_c'.core :=
            hwf'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          simpa only [ModeWatchesInv, hdm_c', ↓reduceIte] using hw_sp
        have hwf_c' : FullWitnessInv c F0 F_cur st_c'.core :=
          fullWitnessInv_of_nw hnw_c' hdm_c' hwat_c'
        have hperm_fc : FullPropDecSpecs.FullArenaPermEq st_fin.core st_c'.core :=
          m7_arenaPermEq_congr rfl rfl rfl rfl hperm'
        have hsc_sem_b : sem_b.scratch = { sem.scratch with
            search_ticks := sem_b.scratch.search_ticks, wsort := sem_b.scratch.wsort,
            phases := sem_b.scratch.phases } := by rw [hpi_b_sc, hs_base]
        have hsc_b' : sem_b.scratch = { s.scratch with
            search_ticks := sem_b.scratch.search_ticks, wsort := sem_b.scratch.wsort,
            phases := sem_b.scratch.phases } := m7_scratch_trans hsc_o hsc_sem_b
        have hsc_c'_b : st_c'.scratch = { sem_b.scratch with
            search_ticks := st_c'.scratch.search_ticks, wsort := st_c'.scratch.wsort,
            phases := st_c'.scratch.phases } := by
          dsimp only [st_c']; rw [hscr_f]
        have hscr_c' : st_c'.scratch = { s.scratch with
            search_ticks := st_c'.scratch.search_ticks, wsort := st_c'.scratch.wsort,
            phases := st_c'.scratch.phases } :=
          m7_scratch_trans hsc_b' hsc_c'_b
        have hpr_c_le : s.core.propagated ≤ st_c'.core.trail_end := by
          rw [← hpr_f]
          have := hlen'.core_ok.propagated_le
          simpa [st_c', st_c_in] using this
        have hmc'_fin : (FullMem c (fastPropMem { s with core :=
            { s.core with trail_end := st_c'.core.trail_end } } st_c') ⋆ R) mc' := by
          simpa only [fastPropMem, st_c', st_c_in, hpr_f, hte_f] using hmc'
        m7c_hsplit
        · have hoom_eq' : oom' = sem_b.core.oom := (hok_t hc).trans hoom_f
          have hperm_bc' : FullPropDecSpecs.FullArenaPermEq sem_b.core st_c'.core :=
            (m7_arenaPermEq_congr rfl rfl har_f halen_f (.refl sem_b.core)).trans hperm_fc
          have hconfl_pres :
              (brk_b = 1#64 → PropLitConfl F_cur ignore_ref st_c'.core ∧
                st_c'.core.oom = 0#64) := fun h1 => by
            have ⟨hcf, hoo⟩ := hbr1 h1
            have hcf' : FullPropDecSpecs.FullConflOkW F_cur st_c'.core := by
              rcases hcf with hne | hok
              · exact absurd hoo hne
              · exact m7_fullConflOkW_of_perm hperm_bc' hcv_f hvals_f
                  hct_f hcr_f hc0_f hc1_f hok.1
            refine ⟨Or.inr ⟨hcf', fun h2 => ?_⟩, ?_⟩
            · rcases hcf with hne | hok
              · exact absurd hoo hne
              · simpa [st_c', hct_f, hcr_f] using hok.2 (by simpa [st_c', hct_f] using h2)
            · simp [st_c', hoom_eq', hoo]
          subst hc
          m7c_hsteps
          exact hJch (brk_b, ()) mc'
            ⟨st_c', hlen_c', hwf_c', ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩,
              hperm_f.trans hperm_fc,
              by simpa only [AgreesExcept, m7CoreMask, st_c'] using hag_s_fin,
              hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
              fun h0 => by
                have ⟨hoo, hct0⟩ := hbr0 h0
                exact ⟨by simp [st_c', hoom_eq', hoo], by simp [st_c', hct_f, hct0]⟩,
              hconfl_pres, fun _ => trivial,
              by rcases hbr_cases with rfl | rfl | rfl <;> simp,
              hpr_f, by simpa [st_c', hs_base] using hag_f.get FullCoreState.fuel,
              by rw [show st_c'.core.probing = st_fin.core.probing from rfl,
                  hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
              hdm_c', hscr_c', st_c'.core.trail_end, Nat.le_refl _, hpr_c_le, hmc'_fin⟩
        · subst hc
          m7c_hsteps
          exact hJch (2#64, ()) mc'
            ⟨st_c', hlen_c', hwf_c', ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩,
              hperm_f.trans hperm_fc,
              by simpa only [AgreesExcept, m7CoreMask, st_c'] using hag_s_fin,
              hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
              fun h => absurd h (by decide), fun h => absurd h (by decide),
              fun _ => trivial, Or.inr (Or.inr rfl),
              hpr_f, by simpa [st_c', hs_base] using hag_f.get FullCoreState.fuel,
              by rw [show st_c'.core.probing = st_fin.core.probing from rfl,
                  hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
              hdm_c', hscr_c', st_c'.core.trail_end, Nat.le_refl _, hpr_c_le, hmc'_fin⟩
      · have hperm_bf : FullPropDecSpecs.FullArenaPermEq sem_b.core st_fin.core :=
          m7_arenaPermEq_congr rfl rfl har_f halen_f (.refl sem_b.core)
        have hsc_fin' : st_fin.scratch = { s.scratch with
            search_ticks := st_fin.scratch.search_ticks, wsort := st_fin.scratch.wsort,
            phases := st_fin.scratch.phases } := by
          rw [hscr_f]
          exact m7_scratch_trans hsc_o (by rw [hpi_b_sc, hs_base])
        m7c_hsteps
        exact hJch (brk_b, ()) mf
          ⟨st_fin, hlen_f, hwf_f, htr_f, hperm_f, hag_s_fin, hcv_f, hvals_f,
            hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
            fun h0 => by
              have ⟨hoo, hct0⟩ := hbr0 h0
              exact ⟨by rw [hoom_f, hoo], by rw [hct_f, hct0]⟩,
            fun h1 => by
              have ⟨hcf, hoo⟩ := hbr1 h1
              refine ⟨?_, by rw [hoom_f, hoo]⟩
              rcases hcf with hne | hok
              · exact absurd hoo hne
              · refine Or.inr ⟨m7_fullConflOkW_of_perm hperm_bf hcv_f hvals_f
                    hct_f hcr_f hc0_f hc1_f hok.1, fun h2 => ?_⟩
                rw [hct_f] at h2; simpa [hcr_f] using hok.2 h2,
            fun _ => trivial, hbr_cases,
            by simpa [hs_base] using hag_f.get FullCoreState.propagated,
            hag_f.get FullCoreState.fuel,
            by rw [hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
            (hag_f.get FullCoreState.dense_mode).trans hdense_b,
            hsc_fin',
            te_mem, Nat.le_trans htem_le (hte_f ▸ hte_sem_le), hpr_tem, hmf⟩
    · have hbr_ne0 : brk_b ≠ 0#64 := by rw [hc]; decide
      have hbr_ne1 : brk_b ≠ 1#64 := by rw [hc]; decide
      subst hc
      have hsc_fin' : st_fin.scratch = { s.scratch with
          search_ticks := st_fin.scratch.search_ticks, wsort := st_fin.scratch.wsort,
          phases := st_fin.scratch.phases } := by
        rw [hscr_f]
        exact m7_scratch_trans hsc_o (by rw [hpi_b_sc, hs_base])
      exact hJch (2#64, ()) mf
        ⟨st_fin, hlen_f, hwf_f, htr_f, hperm_f, hag_s_fin, hcv_f, hvals_f, hte_f,
          hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
          fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun _ => trivial, Or.inr (Or.inr rfl),
          by simpa [hs_base] using hag_f.get FullCoreState.propagated,
          hag_f.get FullCoreState.fuel,
          by rw [hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
          (hag_f.get FullCoreState.dense_mode).trans hdense_b,
          hsc_fin',
          te_mem, Nat.le_trans htem_le (hte_f ▸ hte_sem_le), hpr_tem, hmf⟩

theorem m7_compact_post_ovf_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b : FullState}
    {ignore_ref prop_v te_b un_b uf_b tk_b off_b p_b q_b end_b brk_b t0_v : BitVec 64}
    {not_lit_v : BitVec 32} {not_lit : BitVec 32} {rec_ph : Bool}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64]}
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
      (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
      have s' : FullState :=
        { core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop',
            unassigned := unas', unflushed := unfl', wvec := wvec', arena := arena',
            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
            confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullPropDecSpecs.FullTrailExt s.core s'.core →
      FullPropDecSpecs.FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullPropDecSpecs.FullConflOkW F_cur s'.core ∧
        (ctype' = 2#64 → cref' ≠ ignore_ref) ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept m7CoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
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
      sem_next.scratch = { s.scratch with
        search_ticks := sem_next.scratch.search_ticks,
        wsort := sem_next.scratch.wsort, phases := sem_next.scratch.phases } →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core := { sem_next.core with propagated := s.core.propagated } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var un_b, (.var uf_b,
        (.var tk_b, ())))))) mc0)
    (hwc : c.wcap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7CoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hnl_eq : not_lit_v = not_lit)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hpi_b : PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
      p_b.toNat end_b.toNat)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
    (hmb : (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) :
    wp Γ Q X (m7CompactAndPostOvfExpr J_out c.hdr c.pWstk prop_v te_b un_b uf_b tk_b off_b p_b q_b
      end_b brk_b t0_v not_lit_v rec_ph) mb := by
  subst not_lit_v
  obtain ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ := hs_disk
  have hnot_b : not_lit.toNat < 2 * sem_b.core.cur_vars := by
    rw [hpi_b.cur_vars_eq, hs_base]; exact hnot_lt
  have hend_b_le : end_b.toNat ≤ c.wcap := by
    have := hpi_b.end_lt_wcap hnot_b; omega
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge_b := hpi_b.sw.q_ge
  have hq_le_b := hpi_b.sw.q_le_p
  have hp_le_b := hpi_b.sw.p_le_end
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b.tr.te_ge; subst hs_base; exact this
  have hsd_len : s_disk.LengthsOk c := by
    subst hs_disk_eq
    exact ⟨{ hlen0.core_ok with
        trail_end_le := Nat.le_trans htem_le
          (Nat.le_trans hte_sem_le (by
            rw [← hcv_o]
            have hcv_b : sem_b.core.cur_vars = sem.core.cur_vars := by
              rw [hpi_b.cur_vars_eq, hs_base]
            rw [← hcv_b]
            exact hpi_b.len.core_ok.trail_end_le))
        propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hnot_b_mv : not_lit.toNat < 2 * c.max_vars := by
    have := hpi_b.len.core_ok.cur_vars_le; omega
  have hnl64_1_idx : ((BitVec.setWidth 64 not_lit <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * not_lit.toNat + 1 := by
    simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_add1_nat not_lit
  unfold m7CompactAndPostOvfExpr
  refine wp_loop_group (fun rem_c (pc_v, qc_v, ()) mc =>
    ∃ wstk_c : List (BitVec 32),
      rem_c = end_b.toNat - pc_v.toNat ∧
      wstk_c.length = c.wcap ∧
      p_b.toNat ≤ pc_v.toNat ∧ pc_v.toNat ≤ end_b.toNat ∧
      qc_v.toNat = q_b.toNat + (pc_v.toNat - p_b.toNat) ∧
      (∀ k, off_b.toNat ≤ k → k < q_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k < pc_v.toNat - p_b.toNat, wstk_c[q_b.toNat + k]? = sem_b.core.wstk[p_b.toNat + k]?) ∧
      (∀ k, pc_v.toNat ≤ k → k < end_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k, (k < off_b.toNat ∨ end_b.toNat ≤ k) → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s_disk { sem_b with core :=
        { sem_b.core with wstk := wstk_c } }) ⋆ R) mc) ?_ ?_
  · rintro Jc rem_c ⟨pc_v, qc_v, ⟨⟩⟩ mc ih_c ⟨wstk_c, rfl, hwc_len, hp_pc, hpc_end,
        hqc_n, hpre_c, hsuf_c, hrem_c, hout_c, hmc⟩
    have hmem_c_len : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len
        (sem := { sem_b with core := { sem_b.core with wstk := wstk_c } })
        ⟨{ hpi_b.len.core_ok with wstk_len_arr := hwc_len }, hpi_b.len.scratch_ok⟩
        (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
        (by rw [hs_disk_eq]; dsimp only; rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
        rfl
    have hwc_mem : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).core.wstk.length =
        c.wcap := by rw [fastPropMem_wstk]; exact hwc_len
    m7c_hsplit
    · have hpc_lt : pc_v.toNat < end_b.toNat := hc
      have hpc_lt_w : pc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hqc_lt_w : qc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hpc1_n : (pc_v + 1#64).toNat = pc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      have hqc1_n : (qc_v + 1#64).toNat = qc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      let v_p := wstk_c[pc_v.toNat]'hpc_lt_w
      let wstk_c' := wstk_c.set qc_v.toNat v_p
      have hstep := propLit_loop2_step hq_ge_b hq_le_b hp_pc hpc_lt hpc_lt_w
        (by rw [← hqc_n]; exact hqc_lt_w) hpre_c hsuf_c hrem_c hout_c
      rw [← hqc_n] at hstep
      m7c_hsteps
      exact ih_c _ (pc_v + 1#64, qc_v + 1#64, ()) m (by rw [hpc1_n]; omega)
        ⟨wstk_c', rfl, by simp [wstk_c', hwc_len], by rw [hpc1_n]; omega,
          by rw [hpc1_n]; omega, by rw [hqc1_n, hpc1_n]; omega,
          hstep.1, fun k hk => by rw [hpc1_n] at hk; exact hstep.2.1 k hk,
          fun k hk1 hk2 => by rw [hpc1_n] at hk1; exact hstep.2.2.1 k hk1 hk2,
          hstep.2.2.2, by
            simpa only [wstk_c', v_p, fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
    · have hpc_eq : pc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
      rw [hpc_eq] at hqc_n hsuf_c
      m7c_hsteps_nogrp
      refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
        (BitVec.setWidth 32 (qc_v - off_b)) ?_ hmc) ?_
      next =>
        dsimp only
        erw [hnl64_1_idx]
        rw [fastPropMem_wvec, hpi_b.len.core_ok.wvec_len]
        change 2 * not_lit.toNat + 1 < 4 * c.max_vars; omega
      intro m hm
      dsimp only at hm
      erw [hnl64_1_idx] at hm
      rw [fastPropMem_wvec] at hm
      replace hm : (FullMem c (fastPropMem s_disk
          { sem_b with core :=
            { sem_b.core with
              wstk := wstk_c
              wvec := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
                ((qc_v - off_b).setWidth 32) } }) ⋆ R) m := by
        simpa only [fastPropMem] using hm
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ st_fin : FullState,
            st_fin.LengthsOk c ∧
            FullWitnessInv c F0 F_cur st_fin.core ∧
            AgreesExcept propLitCoreMask s_base.core st_fin.core ∧
            FullPropDecSpecs.FullTrailExt s_base.core st_fin.core ∧
            FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core ∧
            st_fin.core.oom = sem_b.core.oom ∧
            st_fin.core.confl_type = sem_b.core.confl_type ∧
            st_fin.core.confl_ref = sem_b.core.confl_ref ∧
            st_fin.core.confl_lit0 = sem_b.core.confl_lit0 ∧
            st_fin.core.confl_lit1 = sem_b.core.confl_lit1 ∧
            st_fin.core.cur_vars = sem_b.core.cur_vars ∧
            st_fin.core.vals = sem_b.core.vals ∧
            st_fin.core.trail_end = sem_b.core.trail_end ∧
            st_fin.core.unassigned = sem_b.core.unassigned ∧
            st_fin.core.unflushed = sem_b.core.unflushed ∧
            st_fin.core.arena_len = sem_b.core.arena_len ∧
            st_fin.core.cur_level = sem_b.core.cur_level ∧
            st_fin.core.arena = sem_b.core.arena ∧
            st_fin.scratch = sem_b.scratch ∧
            (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) ?_ ?_
      · rintro _ ⟨⟩ mf ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f,
            har_f, hscr_f, hmf⟩
        exact m7_post_ovf_brk_wp hChrono hQ hJ_out hlen0 hpr_lt hs_base
          ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ htr_o hperm_o hag_o hcv_o hcl_o hprob_o
          halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge hpi_b.len hpi_b.cur_vars_eq
          hpi_b.tr hpi_b.sc_eq hdense_b hte_b hun_b
          huf_b hbr0 hbr1 hbr_cases hlen_f hwf_f hag_f htr_f hperm_f hoom_f hct_f hcr_f hc0_f
          hc1_f hcv_f hvals_f hte_f hun_f huf_f halen_f hcl_f har_f hscr_f hmf
      · intro Jfn hJfn
        have hqc_v_eq : qc_v.toNat = q_b.toNat + (end_b.toNat - p_b.toNat) := hqc_n
        have hqc_le_end : qc_v.toNat ≤ end_b.toNat := by omega
        have hidx1_lt : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
            sem_b.core.wvec.length := by
          rw [hpi_b.len.core_ok.wvec_len, m7_bv64_shl1_add1_nat]; omega
        let wvec_f := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
          ((qc_v - off_b).setWidth 32)
        let wu_f := sem_b.core.wusable + (end_b - qc_v)
        m7c_hsplit
        · m7c_hsteps
          refine wp_loop_group (fun rem_k (k_v, ()) mk =>
            ∃ wstk_k : List (BitVec 32),
              rem_k = end_b.toNat - k_v.toNat ∧
              wstk_k.length = c.wcap ∧
              qc_v.toNat ≤ k_v.toNat ∧ k_v.toNat ≤ end_b.toNat ∧
              (∀ i, (i < qc_v.toNat ∨ end_b.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
              (FullMem c (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }) ⋆ R) mk) ?_ ?_
          · rintro Jk rem_k ⟨k_v, ⟨⟩⟩ mk ih_k ⟨wstk_k, rfl, hwk_len, hq_k, hk_end,
                hk_keep, hmk⟩
            have hmem_k_len : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).LengthsOk c :=
              fastPropMem_lengthsOk hsd_len
                (sem := { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } })
                ⟨{ hpi_b.len.core_ok with
                    wvec_len := by simp [wvec_f, hpi_b.len.core_ok.wvec_len]
                    wstk_len_arr := hwk_len },
                 hpi_b.len.scratch_ok⟩
                (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
                (by rw [hs_disk_eq]; dsimp only
                    rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
                rfl
            have hwk_mem : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).core.wstk.length =
                c.wcap := by rw [fastPropMem_wstk]; exact hwk_len
            m7c_hsplit
            · have hk_lt : k_v.toNat < end_b.toNat := hc
              have hk_lt_w : k_v.toNat < wstk_k.length := by rw [hwk_len]; omega
              have hk1_n : (k_v + 1#64).toNat = k_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
              have hk_dec : end_b.toNat - (k_v + 1#64).toNat < end_b.toNat - k_v.toNat := by
                omega
              have hq_k1 : qc_v.toNat ≤ (k_v + 1#64).toNat := by omega
              have hk1_end : (k_v + 1#64).toNat ≤ end_b.toNat := by omega
              refine wp_store_sep
                (FullArenaTactics.c0_store_full_wstk 0xFFFFFFFF#32
                  (by rw [hwk_mem]; exact Nat.lt_of_lt_of_eq hk_lt_w hwk_len) hmk) ?_
              intro m hm
              clear hmk hwk_mem
              m7c_hsteps
              dsimp only [Arg.val] at hm
              exact ih_k (end_b.toNat - (k_v + 1#64).toNat) (k_v + 1#64, ()) m hk_dec
                ⟨wstk_k.set k_v.toNat 0xFFFFFFFF#32, rfl,
                  by rw [List.length_set, hwk_len], hq_k1, hk1_end,
                  propLit_loop3_step hq_k hk_lt hk_keep,
                  by simpa only [fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
            · m7c_hsteps
              have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwk_len
                hqc_v_eq hpre_c hsuf_c hout_c hk_keep
              let st_fin_k : FullState :=
                { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }
              exact hJfn () mk ⟨st_fin_k, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
                rfl, rfl, hmk⟩
          · intro Jk hJk
            exact hJk _ (qc_v, ()) m
              ⟨wstk_c, rfl, hwc_len, Nat.le_refl _, hqc_le_end,
                fun _ _ => rfl,
                by simpa only [wvec_f, wu_f, fastPropMem_wusable, fastPropMem] using hm⟩
        · have hqc_eq_end : qc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
          have hsub0 : end_b - qc_v = 0#64 := by rw [hqc_eq_end]; simp
          have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwc_len
            hqc_v_eq hpre_c hsuf_c hout_c (fun _ _ => rfl)
          have hwu0 : sem_b.core.wusable + (end_b - qc_v) = sem_b.core.wusable := by
            rw [hsub0]; simp
          let st_fin_0 : FullState :=
            { sem_b with core :=
              { sem_b.core with
                wstk := wstk_c, wvec := wvec_f,
                wusable := sem_b.core.wusable + (end_b - qc_v) } }
          exact hJfn () m ⟨st_fin_0, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
            rfl, rfl, by simpa only [st_fin_0, wvec_f, hwu0] using hm⟩
  · intro Jc hJc
    exact hJc _ (p_b, q_b, ()) mb
      ⟨sem_b.core.wstk, rfl, hpi_b.len.core_ok.wstk_len_arr, Nat.le_refl _,
        hp_le_b, by simp, fun _ _ _ => rfl, fun _ hk => absurd hk (by omega),
        fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
