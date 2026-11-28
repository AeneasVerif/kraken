/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduceShared
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Emergency Purge WP Proof (`Proof.Reduce.WpPurge`)

Proves `Func.wp` (`full_reduce_purge_c0_wp`) for `Src.Reduce.full_reduce_purge_c0_body` against
`Spec.fullReducePurgeC0Spec`, using `WpReduceShared` with zero legacy imports.
-/

set_option autoImplicit false

local elab "c0_hsteps_ng" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Reduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped FullArenaTactics

private abbrev PurgePost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
    FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
    s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
    s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
    s'.core.tmp_len = s.core.tmp_len → s'.core.probing = s.core.probing →
    s'.core.min_clr_len = s.core.min_clr_len →
    s'.scratch.work_stk1 = s.scratch.work_stk1 → s'.scratch.work_stk2 = s.scratch.work_stk2 →
    (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
    (0 < s'.core.cur_level →
      s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
      s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
      s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem purge_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext' : List (BitVec 64)} {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64}
    {Q : Post [i64]} (hQ : PurgePost c F0 F_cur s R Q) (hst : RedSt c F0 F_cur s R ext' st ml)
    {r : BitVec 64} (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (hu : r = 20#64 → F0.Unsat) (hoom : r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) :
    Q (r, ()) ml :=
  hQ r ext' st ml hst.inv hr hst.cl hst.fu hst.cv hst.tmp hst.tl hst.prb hst.mcl
    hst.ws1 hst.ws2 hu hoom hst.pos hst.mem

private theorem purge_sweep_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext4 : List (BitVec 64)} {s s4 : FullState}
    {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]} {X : XPost} {Js : Cont []}
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hQ : PurgePost c F0 F_cur s R Q)
    (hJs : ∀ (_ : Tup Val []) mK, (∃ extK sK,
      RedSt c F0 F_cur s R extK sK mK ∧ (s.core.oom = 0#64 → sK.core.oom = 0#64)) → Js () mK)
    (hst4 : RedSt c F0 F_cur s R ext4 s4 m4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun Js_1 => Blocks.cons (fun _ =>
      Expr.jnz (Arg.imm true)
        (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p_6 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_6.fst, Arg.imm 2, ()))
            fun p_7 =>
          Expr.jnz (Arg.var p_7.fst) (Expr.ret (Arg.imm 20, ()))
            (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_6.fst, Arg.imm 3, ()))
              fun p_8 =>
            Expr.jnz (Arg.var p_8.fst) (Expr.ret (Arg.imm 0, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_6.fst, Arg.imm 0, ()))
                fun p_9 =>
              Expr.jnz (Arg.var p_9.fst) (Expr.jump Js ())
                (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                  fun p_10 =>
                  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_10.fst, Arg.imm 1, ()))
                    fun p_11 =>
                  Expr.jnz (Arg.var p_11.fst) (Expr.ret (Arg.imm 20, ()))
                    (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                        (Arg.var p_10.fst, Arg.imm 0, ())) fun p_12 =>
                    Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 0, ()))
                      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                      Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                        (Expr.jump Js_1.fst ())))))))
        (Expr.jump Js ())) .nil) (fun Js_1 => Expr.jump Js_1.fst ())) m4 := by
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ extL st, rem = c.max_vars - st.core.trail_end ∧
      RedSt c F0 F_cur s R extL st ml ∧ (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (0 < st.core.cur_level → FullReasonsMarked st))
    ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨extL, st, rfl, hstL, hoomL, hrmL⟩
    refine wp_jnz_of (fun _ => ?_) (fun h => by cases h)
    refine red_call_sweep13 rfl hSweep hstL hrmL fun sr sA mA hstA hdomA hoomA hposA hsr1 hsr2 => ?_
    c0_hsteps_ng
    · exact purge_finish hQ hstA (Or.inr (Or.inr rfl)) (fun _ => (hsr2 ‹sr = 2#64›).2)
        (fun h => by cases h)
    · exact purge_finish hQ hstA (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
    · exact hJs () mA ⟨extL, sA, hstA, fun _ => hoomA (Or.inl ‹sr = 0#64›)⟩
    · have hsr_eq1 : sr = 1#64 := by
        rcases hdomA with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl0, hst_te_lt⟩ := hsr1 hsr_eq1
      have hoomA0 : sA.core.oom = 0#64 := hoomA (Or.inr hsr_eq1)
      refine red_call_propagate0 rfl hProp hstA hcl0
        fun pr extB sB mB hstB hclB hteB hrB h0B h1B => ?_
      c0_hsteps_ng
      · exact purge_finish hQ hstB (Or.inr (Or.inr rfl)) (fun _ => h1B ‹pr = 1#64›)
          (fun h => by cases h)
      · exact purge_finish hQ hstB (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
      · refine wp_m6Hdr_focus_frame hstB.mem fun hmBf => ?_
        c0_hsteps_ng
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hstB.inv.sparseW.1.core_ok.trail_end_le
            hstB.inv.sparseW.1.core_ok.cur_vars_le
        exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
          ⟨extB, { sB with core := { sB.core with unflushed := 0#64 } }, rfl,
            redSt_with_unflushed hstB 0#64 (fullM6HdrMem_unfocus_full hm),
            fun _ => h0B ‹pr = 0#64› hoomA0,
            fun hpos => by change 0 < sB.core.cur_level at hpos; omega⟩
  · intro L hL
    c0_hsteps_ng
    exact hL (c.max_vars - s4.core.trail_end) () m4 ⟨ext4, s4, rfl, hst4, hoom4, fun _ => hrm4⟩

private theorem purge_mark_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext3 : List (BitVec 64)} {s s3 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [i64]} {X : XPost} {Js_sw : Cont [i64]}
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hJs_sw : ∀ (xs : Tup Val [i64]) m4, (∃ s4 : FullState,
      RedSt c F0 F_cur s R ext3 s4 m4 ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
      FullReasonsMarked s4) → Js_sw xs m4)
    (hst3 : RedSt c F0 F_cur s R ext3 s3 m3)
    (hoom3 : s.core.oom = 0#64 → s3.core.oom = 0#64) (hrm3 : FullReasonsMarked s3) :
    wp Γ Q X (Expr.group (sig := [[i64]]) (fun Js_1 => Blocks.cons (fun p_4 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 48, ())) fun p_5 =>
      Expr.load i64 (Arg.var p_5.fst) fun ld_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_4.fst, Arg.var ld_1, ())) fun p_6 =>
      Expr.jnz (Arg.var p_6.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_7 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_7.fst, ())) fun p_8 =>
        Expr.load i32 (Arg.var p_8.fst) fun ld_2 =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p_4.fst, ())) fun p_9 =>
        Expr.call (as := [i64, i32]) (bs := [i32]) "full_arena_next"
          (Arg.var c.hdr, Arg.var p_9.fst, ()) fun p_10 =>
        Expr.group (sig := [[]]) (fun _Js_2 => Blocks.cons (fun _ =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_10.fst, ())) fun p =>
          Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var p.fst, Arg.var p_4.fst, ()))
            fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Js_sw (Arg.var p_4.fst, ()))
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_10.fst, ())) fun p =>
              Expr.jump Js_1.fst (Arg.var p.fst, ()))) .nil) fun Js =>
        Expr.let_ (Op.mk (.add i64) (Arg.var p_4.fst, Arg.imm 3, ())) fun p_11 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 48, ())) fun p_12 =>
        Expr.load i64 (Arg.var p_12.fst) fun ld_3 =>
        Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var p_11.fst, Arg.var ld_3, ()))
          fun p_13 =>
        Expr.jnz (Arg.var p_13.fst)
          (Expr.let_ (Op.mk (.and i32) (Arg.var ld_2, Arg.imm 4194304, ())) fun p_14 =>
          Expr.let_ (Op.mk (.cmp .ne i32 Ty.bool rfl) (Arg.var p_14.fst, Arg.imm 0, ())) fun p_15 =>
          Expr.jnz (Arg.var p_15.fst)
            (Expr.let_ (Op.mk (.or i32) (Arg.imm 524288, Arg.imm 2097152, ())) fun p_16 =>
            Expr.let_ (Op.mk (.and i32) (Arg.var ld_2, Arg.var p_16.fst, ())) fun p_17 =>
            Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_17.fst, Arg.imm 0, ()))
              fun p_18 =>
            Expr.jnz (Arg.var p_18.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_19 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_19.fst, ())) fun p_20 =>
              Expr.let_ (Op.mk (.or i32) (Arg.var ld_2, Arg.imm 524288, ())) fun p_21 =>
              Expr.store (t := i32) (Arg.var p_21.fst) (Arg.var p_20.fst)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_22 =>
                Expr.load i64 (Arg.var p_22.fst) fun ld_4 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var ld_4, Arg.imm 3, ())) fun p_23 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p_4.fst, Arg.imm 2, ())) fun p_24 =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p_24.fst, Arg.imm 4, ())) fun p_25 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_25.fst, ())) fun p_26 =>
                Expr.load i32 (Arg.var p_26.fst) fun ld =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_27 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p_23.fst, Arg.var p_27.fst, ())) fun p_28 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
                Expr.store (t := i64) (Arg.var p_28.fst) (Arg.var p.fst) (Expr.jump Js.fst ())))
              (Expr.jump Js.fst ()))
            (Expr.jump Js.fst ()))
          (Expr.jump Js.fst ()))
        (Expr.jump Js_sw (Arg.var p_4.fst, ()))) .nil)
      (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ()))) m3 := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  refine wp_loop_inv
    (fun (p, ()) mL =>
      p.toNat ≤ s3.core.arena_len ∧
      (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
      ∃ sL : FullState,
        sL.core.arena_len = s3.core.arena_len ∧
        RedSt c F0 F_cur s R ext3 sL mL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
        FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3)
    (fun (p, ()) _ => s3.core.arena_len - p.toNat)
    (fun JL hLoopL => by
      c0_hsteps_ng
      refine hLoopL (0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3, rfl, hst3, hoom3, hrm3, rfl⟩
      by_cases hz : s3.core.arena_len = 0
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hst3.inv.sparseW.2.1.arena
          (Nat.pos_of_ne_zero hz)))
    (fun JL (p, ()) mL ⟨hp_le, hp_mem, sL, halenL, hstL, hoomL, hrmL, hrefsL⟩ ih => ?_)
  have hlenL := hstL.inv.sparseW.1
  have halL := hlenL.core_ok.arena_len_le
  have haarL := hlenL.core_ok.arena_len_arr
  refine wp_m6Hdr_focus_frame hstL.mem fun hmLf => ?_
  c0_hsteps_ng
  · have hp_lt : p.toNat < sL.core.arena_len := by
      have h := (by assumption : p.toNat < sL.core.arena_len % 2 ^ 64)
      have hmod := Nat.mod_le sL.core.arena_len (2 ^ 64)
      omega
    have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
      rw [hrefsL]; exact hp_mem.resolve_left (by omega)
    have hp_wf := hstL.inv.sparseW.2.1.arena.refs_wf p.toNat hp_in
    have hp_lt32 : p.toNat < 2 ^ 32 := by omega
    have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
    have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
      (cref := p.toNat) hp_wf.1
    have hnxt_mem := fullArenaClauseRefs_next_mem hstL.inv.sparseW.2.1.arena hp_in
    let n32 :=
      BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len (p.setWidth 32).toNat)
    have hn_eq : (n32.setWidth 64).toNat =
        fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
      dsimp only [n32]
      rw [hp_trunc, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hpar_len : p.toNat < sL.core.arena.length := by omega
    refine wp_call_of_spec _ _ ?_
    refine hNext _ _ _ X ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R, rfl, hlenL, hmLf, ?_⟩
    refine wp_join_group
      (fun _ mM => ∃ sM : FullState,
        sM.core.arena_len = s3.core.arena_len ∧
        RedSt c F0 F_cur s R ext3 sM mM ∧ (s.core.oom = 0#64 → sM.core.oom = 0#64) ∧
        FullReasonsMarked sM ∧ fullArenaClauseRefs sM = fullArenaClauseRefs s3)
      (fun _ _ mM ⟨sM, halenM, hstM, hoomM, hrmM, hrefsM⟩ => by
        c0_hsteps_ng
        · exfalso
          have h := (by assumption :
            fullArenaNextOff sL.core.arena sL.core.arena_len
              (BitVec.toNat (Arg.var (t := i32) (p.setWidth 32)).val) % 2 ^ 32 ≤ p.toNat)
          dsimp only [Arg.val] at h
          rw [hp_trunc, Nat.mod_eq_of_lt (by omega)] at h
          omega
        · exact ih (n32.setWidth 64, ()) mM (by dsimp only [Arg.val]; rw [hn_eq]; omega)
            ⟨by rw [hn_eq]; omega,
              by rw [hn_eq]
                 rcases hnxt_mem with hend | hmem
                 · exact Or.inl (hend.trans halenL)
                 · exact Or.inr (hrefsL ▸ hmem),
              sM, halenM, hstM, hoomM, hrmM, hrefsM⟩)
      (fun JM hJM => ?_)
    c0_hsteps_ng
    · have hmask2 : (sL.core.arena[p.toNat]'hpar_len &&& 0x00280000#32) = 0#32 := by
        have h := (by assumption :
          (sL.core.arena[p.toNat]'hpar_len &&& (524288#32 ||| 2097152#32)) = 0#32)
        simpa [show (524288#32 ||| 2097152#32 : BitVec 32) = 0x00280000#32 by decide] using h
      have hp2_ar : p.toNat + 2 < sL.core.arena.length := by have := hp_wf.1; omega
      have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
        rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hp2_ar64 : (p + 2#64).toNat < sL.core.arena.length := by rw [hp2_eq]; exact hp2_ar
      have hhdr_eq : sL.core.arena[p.toNat]'hpar_len = fullArenaHdr sL p.toNat := by
        unfold fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem hpar_len, Option.getD_some]
      have hnorsn : (fullArenaHdr sL p.toNat &&& 0x00200000#32) = 0#32 := by
        rw [← hhdr_eq]; exact bv32_norsn_of_and_280000 hmask2
      c0_hsteps_ng
      obtain ⟨hstM, hrmM, hrefsM, _⟩ :=
        redSt_mark_garb (rc := 0) (agN := _) hstL hrmL (fun _ h => by simp at h)
          hp_in hnorsn hpar_len (fullM6HdrMem_unfocus_full hm)
      exact hJM () m ⟨_, by simpa using halenL, hstM, hoomL, hrmM, hrefsM.trans hrefsL⟩
    all_goals exact hJM () mL ⟨sL, halenL, hstL, hoomL, hrmL, hrefsL⟩
  · exact hJs_sw (p, ()) mL ⟨sL, hstL, hoomL, hrmL⟩

private theorem purge_unflushed_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {Js : Cont []}
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hQ : PurgePost c F0 F_cur s R Q)
    (hJs : ∀ (_ : Tup Val []) m1, (∃ ext1 s1,
      RedSt c F0 F_cur s R ext1 s1 m1 ∧ (s.core.oom = 0#64 → s1.core.oom = 0#64)) → Js () m1)
    (hinv0 : FullM6HdrInvW c F0 F_cur ext0 s) (hm0 : (FullM6HdrMem c ext0 s ⋆ R) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_2 =>
      Expr.jnz (Arg.var p_2.fst)
        (Expr.group (sig := [[]]) (fun _Js_1 => Blocks.cons (fun _p_3 =>
          Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ()) fun p_4 =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_4.fst, Arg.imm 1, ()))
              fun p_5 =>
            Expr.jnz (Arg.var p_5.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_4.fst, Arg.imm 0, ()))
                fun p_6 =>
              Expr.jnz (Arg.var p_6.fst) (Expr.ret (Arg.imm 0, ()))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump Js ())))) .nil)
          fun Js_1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 160, ())) fun p_3 =>
          Expr.load i64 (Arg.var p_3.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_4 =>
          Expr.jnz (Arg.var p_4.fst)
            (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
              (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.jump Js_1.fst ())
            (Expr.jump Js_1.fst ()))
        (Expr.jump Js ())) m := by
  have hst0 := redSt_refl hinv0 hm0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hsteps_ng
  · refine wp_join_group (fun _ mB => ∃ sB,
        RedSt c F0 F_cur s R ext0 sB mB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64))
      (fun _ _ mB ⟨sB, hstB, hclB, hoomB⟩ => by
        refine red_call_propagate0 rfl hProp hstB hclB
          fun pr extP sP mP hstP _ _ hrP h0P h1P => ?_
        c0_hsteps_ng
        · exact purge_finish hQ hstP (Or.inr (Or.inr rfl)) (fun _ => h1P ‹pr = 1#64›)
            (fun h => by cases h)
        · exact purge_finish hQ hstP (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
        · refine wp_m6Hdr_focus_frame hstP.mem fun hmPf => ?_
          c0_hsteps_ng
          exact hJs () _ ⟨extP, { sP with core := { sP.core with unflushed := 0#64 } },
            redSt_with_unflushed hstP 0#64 (fullM6HdrMem_unfocus_full hm),
            fun hso => h0P ‹pr = 0#64› (hoomB hso)⟩)
      (fun JB hJB => by
        c0_hsteps_ng
        · refine red_call_backtrack0 rfl hBt hst0 fun sB mB hstB hclB hoomB_eq => ?_
          exact hJB () mB ⟨sB, hstB, hclB, fun h => hoomB_eq ▸ h⟩
        · have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
          have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
            have := hinv0.sparseW.2.1.cur_level_le
            have := hinv0.sparseW.1.core_ok.trail_end_le
            have := hinv0.sparseW.1.core_ok.cur_vars_le; omega
          have h := (by assumption : ¬ (0#64 : BitVec 64).toNat < s.core.cur_level % 2 ^ 64)
          have hcl0 : s.core.cur_level = 0 := by
            rw [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt hcl_lt64] at h
            omega
          exact hJB () m ⟨s, hst0, hcl0, id⟩)
  · exact hJs () m ⟨ext0, s, hst0, id⟩

/-- `full_reduce_purge_c0` satisfies `Spec.reducePurgeSpec`. -/
public theorem full_reduce_purge_c0_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hMark : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, Spec.reducePurgeSpec a m Q X →
      Func.wp Γ full_reduce_purge_c0_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext0, s, ⟨F0, F_cur⟩, R, rfl, _hcfg0, _hext0, _hlen0, hinv0, hm0, hQ0⟩ :=
    M6HdrContract.elim hs
  let hQ : PurgePost c F0 F_cur s R Q :=
    fun r ext' s' m' hinv' hr hcl hfu hcv htmp htl hprb hmcl hws1 hws2 hu hoom hpos hm' =>
      hQ0 (r, ()) ext' s' m' hinv'.toInv.2.1 trivial hinv'.toInv.2.2.1.lengths
        ⟨hr, hfu, hu, ⟨hinv', hcl, hcv, htmp, htl, hprb, hmcl, hws1, hws2, hoom, hpos⟩⟩ hm'
  unfold Func.wp full_reduce_purge_c0_body
  dsimp only
  refine wp_join_group (fun _ m1 => ∃ ext1 s1,
      RedSt c F0 F_cur s R ext1 s1 m1 ∧ (s.core.oom = 0#64 → s1.core.oom = 0#64)) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hst1, hoom1⟩
    refine red_call_mark_reasons rfl hMark hst1 fun s3 m3 hst3 hrm3 hoom3_eq => ?_
    have hrm3' : FullReasonsMarked s3 := hrm3 rfl
    have hoom3 : s.core.oom = 0#64 → s3.core.oom = 0#64 := fun h => hoom3_eq.trans (hoom1 h)
    refine wp_m6Hdr_focus_frame hst3.mem fun hm3f => ?_
    c0_hsteps_ng
    refine wp_join_group (ts := [i64]) (fun _ m4 => ∃ s4 : FullState,
        RedSt c F0 F_cur s R ext1 s4 m4 ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
        FullReasonsMarked s4) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ m4 ⟨s4, hst4, hoom4, hrm4⟩
      refine wp_join_group (fun _ mK => ∃ extK sK,
          RedSt c F0 F_cur s R extK sK mK ∧ (s.core.oom = 0#64 → sK.core.oom = 0#64))
        (fun _ _ mK ⟨extK, sK, hstK, hoomK⟩ => by
          c0_hsteps_ng
          exact purge_finish hQ hstK (Or.inr (Or.inl rfl)) (fun h => by cases h)
            (fun _ => hoomK))
        (fun _ hJs =>
          purge_sweep_loop_wp hProp hSweep hQ (fun _ mK h => hJs () mK h) hst4 hoom4 hrm4)
    · exact fun Js_sw hJs_sw => purge_mark_loop_wp hNext hJs_sw hst3 hoom3 hrm3'
  · exact fun Js hJs => purge_unflushed_wp hBt hProp hQ hJs hinv0 hm0

end LeanQbe.T.Examples.Kissat.Proof.Reduce
