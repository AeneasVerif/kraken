/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Shared OTFS Helpers & `full_otfs_bin_wp` (`Proof.Deduce.WpOtfsBin`)

Defines shared watch-stack headroom / BitVec / opaque-state OTFS lemmas (reused by `WpOtfsLarge0/1`)
and proves `full_otfs_bin_wp` against `Spec.fullOtfsBinSpec` (`public section`, `0` legacy imports,
`0` `import all`, `0` `@[expose]` on theorems/lemmas/sections, every declaration `<= 450` LOC).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. Shared OTFS State, Watch-Stack Headroom & BitVec Helpers -/

theorem otfs_opaque_state {c : FullCfg} {s_old : FullState} (k_new : FullCoreState)
    (sc_new : FullScratch) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s_old ⋆ R) m) (hc : s_old.core = k_new) (hs : s_old.scratch = sc_new) :
    ∃ s_new : FullState,
      s_new.core = k_new ∧ s_new.scratch = sc_new ∧ (FullMem c s_new ⋆ R) m :=
  ⟨{ core := k_new, scratch := sc_new }, rfl, rfl, fullMem_of_eq hm hc hs⟩

theorem otfs_unwatch_fin_mem {c : FullCfg} {sL s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {ws0 ws1 ws2 ws3 wv1 wv2 : List (BitVec 32)} {wu1 wu2 : BitVec 64}
    (hm : (FullMem c
      { { { { sL with core := { sL.core with wstk := ws1 } } with
          core := { { sL with core := { sL.core with wstk := ws1 } }.core with wstk := ws2 } } with
          core := { { { sL with core := { sL.core with wstk := ws1 } } with
            core := { { sL with core := { sL.core with wstk := ws1 } }.core with
              wstk := ws2 } }.core with wvec := wv1 } } with
          core := { { { { sL with core := { sL.core with wstk := ws1 } } with
            core := { { sL with core := { sL.core with wstk := ws1 } }.core with
              wstk := ws2 } } with
            core := { { { sL with core := { sL.core with wstk := ws1 } } with
              core := { { sL with core := { sL.core with wstk := ws1 } }.core with
                wstk := ws2 } }.core with wvec := wv1 } }.core with wusable := wu1 } } ⋆ R) m)
    (hk : sL.core = { s.core with wstk := ws0 }) (hsc : sL.scratch = s.scratch)
    (hws : ws2 = ws3) (hwv : wv1 = wv2) (hwu : wu1 = wu2) :
    (FullMem c { s with core := { s.core with wvec := wv2, wstk := ws3, wusable := wu2 } } ⋆ R) m :=
  fullMem_of_eq hm (by
    cases sL with
    | mk cL scL => dsimp only at hk hsc ⊢; subst hk hws hwv hwu; rfl) hsc

theorem otfs_list_getElem_of_list_idx {α : Type} {xs ys : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < ys.length} (hl : xs = ys) (hij : i = j) :
    xs[i]'hi = ys[j]'hj := by
  subst hl; subst hij; rfl

theorem otfs_bv64_add1_nat (x : BitVec 64) (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

theorem otfs_bv64_shl_sext1 (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  have hs : BitVec.signExtend 64 1#32 = (1 : BitVec 64) := by decide
  have hsh : x <<< (1 : BitVec 64) = x <<< (1 : Nat) := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hs, hsh]
  exact bv64_shl1_nat x h

theorem otfs_bv64_shl_sext1_add1 (x : BitVec 64) (h : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< BitVec.signExtend 64 1#32) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hs := otfs_bv64_shl_sext1 x (by omega)
  rw [BitVec.toNat_add, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

theorem otfs_wstack_ensure2_ret_false_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Jd : Cont []}
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hmw : ModeWatchesInv F_cur s.core) (hm : (FullMem c s ⋆ R) m)
    (hOom : ∀ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
      (wu_i : BitVec 64) (wso_i : List (BitVec 32)) (ml_o : Mem 64),
      s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } →
      s_i.scratch = { s.scratch with wsort := wso_i } →
      s_i.LengthsOk c → ModeWatchesInv F_cur s_i.core →
      (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o →
      Q (false, ()) ml_o)
    (hJd : ∀ xs ml_d,
      (∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧
        (FullMem c s_d ⋆ R) ml_d) →
      Jd xs ml_d) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_19 =>
       Expr.load i64 (Arg.var p_19.fst) fun ld =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_20 =>
       Expr.load i64 (Arg.var p_20.fst) fun ld_5 =>
       Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_5, ())) fun p_21 =>
       Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_21.fst, Arg.imm 2, ())) fun p_22 =>
       Expr.jnz (Arg.var p_22.fst)
         (Expr.group (fun (_ : Tup Cont [[]]) =>
             Blocks.cons (fun (_ : Tup Val []) =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_24 =>
               Expr.load i64 (Arg.var p_24.fst) fun ld =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_25 =>
               Expr.load i64 (Arg.var p_25.fst) fun ld_6 =>
               Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_6, ())) fun p_26 =>
               Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                 (Arg.var p_26.fst, Arg.imm 2, ())) fun p_27 =>
               Expr.jnz (Arg.var p_27.fst)
                 (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                    (Expr.ret (Arg.imm false, ())))
                 (Expr.jump Jd ())) Blocks.nil)
           fun Js =>
           Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_23 =>
           Expr.load i64 (Arg.var p_23.fst) fun ld =>
           Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_24 =>
           Expr.jnz (Arg.var p_24.fst)
             (Expr.call (rs := [.bool]) (as := [i64]) (bs := [])
               "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
               Expr.jump Js.fst ())
             (Expr.jump Js.fst ()))
         (Expr.jump Jd ())) m := by
  have hcv_lt32 : s.core.cur_vars < 2 ^ 32 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  have hwcap_lt64 : c.wcap < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at *; omega
  have hwlen_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hlay0 : WatchStackLayout s.core := by
    have h := hmw; unfold ModeWatchesInv at h
    simp only [hdm, ↓reduceIte] at h; exact h.layout
  c0_hsteps_nogrp
  · refine wp_join_group (ts := []) (fun () ml_i =>
      ∃ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
        (wu_i : BitVec 64) (wso_i : List (BitVec 32)),
        s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } ∧
        s_i.scratch = { s.scratch with wsort := wso_i } ∧
        s_i.LengthsOk c ∧ ModeWatchesInv F_cur s_i.core ∧ (FullMem c s_i ⋆ R) ml_i) ?_ ?_
    · rintro _ ⟨⟩ ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
      have hwli_le : s_i.core.wlen ≤ c.wcap := hlen_i.core_ok.wlen_le
      c0_hsteps
      · exact hOom s_i wv_i ws_i wl_i wu_i wso_i _ hsi_c hsi_sc hlen_i hmw_i (by assumption)
      · exact hJd () ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
    · intro Ji hJi
      c0_hsteps_nogrp
      · c0_call hDefrag
        refine ⟨c, s, R, rfl, hlen, hlay0, hm,
          fun wv_i ws_i wl_i wso_i ml_i hlen_i hlay_i _ hpres hm_i => ?_⟩
        obtain ⟨s_i, hsi_c, hsi_sc, hm_i'⟩ :=
          otfs_opaque_state (s_old := { s with
            core := { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            scratch := { s.scratch with wsort := wso_i } })
            { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            { s.scratch with wsort := wso_i } hm_i rfl rfl
        have hmw_i : ModeWatchesInv F_cur s_i.core := by
          rw [hsi_c]
          exact fullWstackDefrag_preserves_modeWatchesInv hmw hlay_i rfl rfl (fun _ hr => hr) hpres
        have hlen_i' : s_i.LengthsOk c :=
          ⟨by rw [hsi_c]; exact hlen_i.core_ok, by rw [hsi_sc]; exact hlen_i.scratch_ok⟩
        exact hJi () ml_i ⟨s_i, wv_i, ws_i, wl_i, 0#64, wso_i, hsi_c, hsi_sc, hlen_i', hmw_i,
          hm_i'⟩
      · exact hJi () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
          s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩
  · exact hJd () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
      s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩

/-! ## 2. `full_otfs_bin_wp` (`Spec.fullOtfsBinSpec`) -/

private theorem otfs_bin_watchSlice_tail {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len) :
    (∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k lit (p + 1) (len - 1)) ∨
    (2 ≤ len ∧ ∃ w0 cr, k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧ WatchSliceOk F_cur k lit (p + 2) (len - 2)) := by
  cases h with
  | empty => omega
  | bin hp hflag hne hlt hent hrest =>
    exact Or.inl ⟨_, hp, hflag, hne, hlt, hent, by simpa using hrest⟩
  | large hp hp1 hflag hlt href hrest =>
    exact Or.inr ⟨Nat.le_add_left 2 _, _, _, hp, hp1, hflag, hlt, href, by simpa using hrest⟩

private theorem otfs_bin_oom_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv ws : List (BitVec 32)} {wl : Nat} {wu : BitVec 64} {wso : List (BitVec 32)}
    {m' : Mem 64} (hiu : idx_u < cut) (hnd : FullArenaVarsNodup s)
    (hlen_in : ({ s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu },
      scratch := { s.scratch with wsort := wso } } : FullState).LengthsOk c)
    (hw_in : FullWitnessCutInv c F0 F_cur cut
      { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu })
    (hm' : (FullMem c { s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := 1#64 },
      scratch := { s.scratch with wsort := wso } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core →
      FullArenaVarsNodup s' → FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (false, ()) m' :=
  hQ false s.core.arena s.core.arena_garbage wv ws wl wu s.core.num_binary
    s.core.confl_type s.core.confl_ref s.core.confl_lit0 s.core.confl_lit1 1#64
    { s.scratch with wsort := wso } m' ⟨{ hlen_in.core_ok with }, hlen_in.scratch_ok⟩
    (fcut_shrink_cut (fcut_with_oom hw_in 1#64) (Nat.le_of_lt hiu))
    (by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
          fullArenaClauseLits
        exact hnd)
    ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm'

private theorem otfs_bin_mark_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv4 ws4 : List (BitVec 32)} {wl4 : Nat} {wu4 nb4 : BitVec 64} {wso4 : List (BitVec 32)}
    {gsz : BitVec 64} {m' : Mem 64} (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s)
    {cref uip f0 f1 : BitVec 32} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (_hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hf0_m : f0.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf1_m : f1.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf0_u : f0 ≠ uip) (hf1_u : f1 ≠ uip)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hf1_lt : f1.toNat < 2 * s.core.cur_vars)
    (hent_f : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (har_len : s.core.arena.length = c.arena_cap) (_h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hcr0_bd : (cref.setWidth 64).toNat < s.core.arena.length)
    (hlen4 : ({ s with
      core := { s.core with num_binary := nb4, wvec := wv4, wstk := ws4,
                            wlen := wl4, wusable := wu4 }
      scratch := { s.scratch with wsort := wso4 } } : FullState).LengthsOk c)
    (hw4 : FullWitnessCutInv c F0 F_cur cut
      { s.core with num_binary := nb4, wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 })
    (hm' : (FullMem c { s with
      core := { s.core with
        num_binary := nb4, wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4,
        arena := s.core.arena.set (cref.setWidth 64).toNat
          (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32),
        arena_garbage := s.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso4, otfs_cnt := s.scratch.otfs_cnt + 1#64 } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core →
      FullArenaVarsNodup s' → FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (true, ()) m' := by
  let s4 : FullState :=
    { s with
      core := { s.core with num_binary := nb4, wvec := wv4, wstk := ws4,
                            wlen := wl4, wusable := wu4 }
      scratch := { s.scratch with wsort := wso4 } }
  have hna := otfs_nonactive_on_trail hw4 hlen4.core_ok hiu_cut hiu_te ht_u hr_u hlev_u hcref
  obtain ⟨arena5, h_arena5⟩ : ∃ xs, xs = s4.core.arena.set cref.toNat
      (fullArenaHdrCore s4.core cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
  let ag5 := s.core.arena_garbage + gsz
  have hcr_toNat : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr_lt_len : cref.toNat < s.core.arena.length := hcr_toNat ▸ hcr0_bd
  have hd_c : fullArenaHdrCore s4.core cref.toNat =
      s.core.arena[cref.toNat]'hcr_lt_len := by
    unfold fullArenaHdrCore; dsimp only [s4]
    rw [List.getElem?_eq_getElem hcr_lt_len, Option.getD_some]
  have hmg5 := markGarb_preserves_fullWitnessCut hlen4.core_ok
    (fcut_shrink_cut hw4 (Nat.le_of_lt hiu_cut)) hcref ag5 fun idx hidx hc =>
    hna idx hidx (hc.elim (fun h => Or.inl (Nat.lt_min.mpr ⟨Nat.lt_trans h hiu_cut, h⟩)) Or.inr)
  rw [← h_arena5] at hmg5
  obtain ⟨hw5_a, hrefs5, hprops5⟩ := hmg5
  have hgarb5 : fullArenaClauseGarbCore
      { s4.core with arena := arena5, arena_garbage := ag5 } cref.toNat = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [h_arena5]; dsimp only [s4]
    rw [List.getElem?_set_self (by simpa [har_len] using hcr_lt_len), Option.getD_some]
    simp [bv32_or_garb_garb]
  let s5_pre : FullState :=
    { s4 with core := { s4.core with arena := arena5, arena_garbage := ag5 } }
  have hnd4_ana : FullArenaVarsNodup s4 := fun r hr hgr =>
    hnd r (by change r ∈ fullArenaClauseRefsCore s.core
              simpa [fullArenaClauseRefsCore, s4] using hr)
      (by change fullArenaClauseGarbCore s.core r = false
          simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s4] using hgr)
  have hnd5_pre : FullArenaVarsNodup s5_pre := fullArenaVarsNodup_markGarb
    hnd4_ana hrefs5 hgarb5 fun r hr hne => ⟨(hprops5 r hr).2.2 hne, (hprops5 r hr).2.1⟩
  have hw_fin : FullWitnessCutInv c F0 F_cur idx_u
      { s.core with
        arena := arena5, arena_garbage := ag5, num_binary := nb4,
        wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4, confl_type := 1#64,
        confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 } :=
    fcut_with_confl hw5_a 1#64 (f0.setWidth 64) (f1.setWidth 64) 0xFFFFFFFF#64
  let s_fin : FullState :=
    { s with
      core :=
        { s.core with
          arena := arena5, arena_garbage := ag5, num_binary := nb4,
          wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4, confl_type := 1#64,
          confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso4, otfs_cnt := s.scratch.otfs_cnt + 1#64 } }
  have harena := c.harena; unfold dimacsBound at harena
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_le := hlen4.core_ok.arena_len_le
  have hcr_lt : cref.toNat < 2 ^ 31 - 1 := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr_lt
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (Nat.lt_trans hcr_lt (by omega))).2.2
  have hri := hw.reason_inv_cut idx_u hiu_cut
  dsimp only at hri; rw [ht_u, hr_u] at hri
  have hri := hri hcref_ne
  rw [ite_eq_right (fun h => absurd hcref_lg h)] at hri
  have hconfl_ok : FullConflictOkCut F_cur idx_u s_fin := by
    simp only [FullConflictOkCut, FullConflictOkW, s_fin, ↓reduceIte]
    have hto0 : (f0.setWidth 64).toNat = f0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hto1 : (f1.setWidth 64).toNat = f1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    rw [hto0, hto1]
    have hm_ex (f : BitVec 32) (hfm : f.toNat ∈ fullArenaClauseLits s cref.toNat)
        (hfu : f ≠ uip) (hflt : f.toNat < 2 * s.core.cur_vars) :
        s.core.vals[f.toNat]?.getD 0#8 = 0xFF#8 ∧
        ((s.core.lvl[f.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
          ∃ m < idx_u, (s.core.trl[m]?.getD 0#32).toNat = f.toNat ^^^ 1) := by
      have hneq : f.toNat ≠ uip.toNat := fun he => hfu (BitVec.eq_of_toNat_eq he)
      obtain ⟨m0, hm0, hm0_eq, _⟩ := (hri.2.2 f.toNat hfm).resolve_left hneq
      exact ⟨(hw.vals_false_iff f.toNat hflt).mpr ⟨m0, Nat.lt_trans hm0 hiu_te, hm0_eq⟩,
        fun _ => ⟨m0, hm0, hm0_eq⟩⟩
    have p0 := hm_ex f0 hf0_m hf0_u hf0_lt
    have p1 := hm_ex f1 hf1_m hf1_u hf1_lt
    refine ⟨Or.inl ⟨trivial, hf0_lt, hf1_lt, p0.1, p1.1, hent_f⟩, ?_⟩
    exact ⟨p0.2, p1.2⟩
  have hlen_fin : s_fin.LengthsOk c :=
    ⟨{ hlen4.core_ok with arena_len_arr :=
        (by dsimp [s_fin]; rw [h_arena5]; dsimp [s4]; simp [har_len]) },
      { hlen4.scratch_ok with }⟩
  have hnd_fin : FullArenaVarsNodup s_fin := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact hnd5_pre
  have har5_eq : s.core.arena.set (cref.setWidth 64).toNat
      (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32) = arena5 := by
    rw [h_arena5]; dsimp only [s4]
    exact list_set_congr hcr_toNat
      (by rw [hd_c, getElem_eq_of_idx hcr_toNat])
  exact hQ true arena5 ag5 wv4 ws4 wl4 wu4 nb4 1#64 0xFFFFFFFF#64
    (f0.setWidth 64) (f1.setWidth 64) s.core.oom s_fin.scratch m' hlen_fin hw_fin hnd_fin
    ⟨rfl, rfl⟩ rfl rfl rfl hrefs5 (fun _ => ⟨rfl, hconfl_ok⟩)
    (fullMem_of_eq hm' (by dsimp [s_fin, ag5]; rw [har5_eq]) rfl)

private theorem otfs_bin_tail_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut idx_u : Nat} {s s2 : FullState}
    {wv2 ws2 : List (BitVec 32)} {wl2 : Nat} {wu2 nb2 : BitVec 64} {wso2 : List (BitVec 32)}
    {cref uip f0 f1 : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {m2 : Mem 64}
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hUnw : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hdm : s.core.dense_mode = 0#64)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hf0_m : f0.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf1_m : f1.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf0_u : f0 ≠ uip) (hf1_u : f1 ≠ uip)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hf1_lt : f1.toNat < 2 * s.core.cur_vars)
    (hent_f : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (har_len : s.core.arena.length = c.arena_cap) (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hs2_c : s2.core = { s.core with
      wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2, num_binary := nb2 })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso2 })
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core →
      FullArenaVarsNodup s' → FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    wp Γ Q X
      (.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_44 =>
       .let_ (Op.mk (.add i64) (Arg.var p_44.fst, Arg.imm 3, ())) fun p_45 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ())) fun p_46 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_46.fst, ())) fun p_47 =>
       .load i32 (Arg.var p_47.fst) fun ld_9 =>
       .call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
         (Arg.var c.hdr, Arg.var ld_9, Arg.var cref, ()) fun _ =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_49 =>
       .let_ (Op.mk (.add i64) (Arg.var p_49.fst, Arg.imm 4, ())) fun p_50 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_50.fst, Arg.imm 4, ())) fun p_51 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_51.fst, ())) fun p_52 =>
       .load i32 (Arg.var p_52.fst) fun ld_10 =>
       .call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
         (Arg.var c.hdr, Arg.var ld_10, Arg.var cref, ()) fun _ =>
       .call (as := [i64, i32]) (bs := [i32]) "full_arena_next"
         (Arg.var c.hdr, Arg.var cref, ()) fun p_54 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var p_54.fst, ())) fun p_55 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_56 =>
       .let_ (Op.mk (.sub i64) (Arg.var p_55.fst, Arg.var p_56.fst, ())) fun p_57 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_58 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_58.fst, Arg.imm 4, ())) fun p_59 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_59.fst, ())) fun p_60 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_61 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_61.fst, Arg.imm 4, ())) fun p_62 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_62.fst, ())) fun p_63 =>
       .load i32 (Arg.var p_63.fst) fun ld =>
       .let_ (Op.mk (.or i32) (Arg.var ld, Arg.imm 524288#32, ())) fun p_64 =>
       .store (Arg.var p_64.fst) (Arg.var p_60.fst)
       (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_65 =>
        .load i64 (Arg.var p_65.fst) fun ld =>
        .let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_57.fst, ())) fun p_66 =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_67 =>
        .store (Arg.var p_66.fst) (Arg.var p_67.fst)
        (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p_68 =>
         .store (Arg.imm (t := i64) 1#64) (Arg.var p_68.fst)
         (.let_ (Op.mk (.zext 32 64) (Arg.var f0, ())) fun p_69 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 536, ())) fun p_70 =>
          .store (Arg.var p_69.fst) (Arg.var p_70.fst)
          (.let_ (Op.mk (.zext 32 64) (Arg.var f1, ())) fun p_71 =>
           .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 544, ())) fun p_72 =>
           .store (Arg.var p_71.fst) (Arg.var p_72.fst)
           (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ())) fun p_73 =>
            .store (Arg.imm (t := i64) 0xFFFFFFFF#64) (Arg.var p_73.fst)
            (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 960, ())) fun p_74 =>
             .load i64 (Arg.var p_74.fst) fun ld =>
             .let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1#64, ())) fun p_75 =>
             .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 960, ())) fun p =>
             .store (Arg.var p_75.fst) (Arg.var p.fst)
             (.ret (Arg.imm true, ()))))))))) m2 := by
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have harena := c.harena; unfold dimacsBound at harena
  have har_le : s.core.arena_len ≤ c.arena_cap := by
    have h := hlen2.core_ok.arena_len_le; rwa [hs2_c] at h
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s2.core.arena.length := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide), show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), hs2_c]; dsimp only
    rw [har_len]; omega
  have hlay2 : WatchStackLayout s2.core := by
    have h := hw2.watches; unfold ModeWatchesInv at h
    rw [ite_eq_left (show s2.core.dense_mode = 0#64 by rw [hs2_c]; exact hdm)] at h
    exact h.layout
  c0_hsteps_nogrp
  c0_call hUnw
  refine ⟨c, s2, R, rfl, hlen2, hlay2, hm2, fun wv3 ws3 wu3 m3 hlen3 hlay3 hmw3 hm3 => ?_⟩
  clear hm2
  obtain ⟨s3, hs3_c, hs3_sc, hm3'⟩ :=
    otfs_opaque_state (s_old := { s2 with
      core := { s2.core with wvec := wv3, wstk := ws3, wusable := wu3 } })
      { s2.core with wvec := wv3, wstk := ws3, wusable := wu3 } s2.scratch hm3 rfl rfl
  have hs3_base : s3.core = { s.core with
      wvec := wv3, wstk := ws3, wlen := wl2, wusable := wu3, num_binary := nb2 } := by
    rw [hs3_c, hs2_c]
  have hs3_sc' : s3.scratch = { s.scratch with wsort := wso2 } := hs3_sc.trans hs2_sc
  have hw3 : FullWitnessCutInv c F0 F_cur cut s3.core := by
    rw [hs3_c]; exact fcut_with_watches hw2 (hmw3 F_cur hw2.watches)
  have hlen3' : s3.LengthsOk c :=
    ⟨by rw [hs3_c]; exact hlen3.core_ok, by rw [hs3_sc]; exact hlen3.scratch_ok⟩
  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide), show (4#64 : BitVec 64).toNat = 4 from rfl,
      Nat.mod_eq_of_lt (by omega), hs3_base]; dsimp only; rw [har_len]; omega
  c0_hsteps_nogrp
  c0_call hUnw
  refine ⟨c, s3, R, rfl, hlen3', by rw [hs3_c]; exact hlay3, hm3',
    fun wv4 ws4 wu4 m4 hlen4 _ hmw4 hm4 => ?_⟩
  clear hm3'
  obtain ⟨s4, hs4_c, hs4_sc, hm4'⟩ :=
    otfs_opaque_state (s_old := { s3 with
      core := { s3.core with wvec := wv4, wstk := ws4, wusable := wu4 } })
      { s3.core with wvec := wv4, wstk := ws4, wusable := wu4 } s3.scratch hm4 rfl rfl
  have hs4_base : s4.core = { s.core with
      wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4, num_binary := nb2 } := by
    rw [hs4_c, hs3_base]
  have hs4_sc' : s4.scratch = { s.scratch with wsort := wso2 } := hs4_sc.trans hs3_sc'
  have hw4 : FullWitnessCutInv c F0 F_cur cut s4.core := by
    rw [hs4_c]; exact fcut_with_watches hw3 (hmw4 F_cur hw3.watches)
  have hlen4' : s4.LengthsOk c :=
    ⟨by rw [hs4_c]; exact hlen4.core_ok, by rw [hs4_sc]; exact hlen4.scratch_ok⟩
  c0_call hNext
  refine ⟨c, s4, R, rfl, hlen4', hm4', ?_⟩
  let nxt := BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len cref.toNat)
  let gsz := nxt.setWidth 64 - cref.setWidth 64
  have hcr0_bd : (cref.setWidth 64).toNat < s4.core.arena.length := by
    rw [zext_toNat cref (by decide), hs4_base]; dsimp only; rw [har_len]; omega
  have hcr0_s : (cref.setWidth 64).toNat < s.core.arena.length := by
    rw [zext_toNat cref (by decide), har_len]; omega
  c0_hsteps
  let s_lfin : FullState :=
    { s4 with
      core := { s4.core with
        arena := s4.core.arena.set (cref.setWidth 64).toNat
          (s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32),
        arena_garbage := s4.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 }
      scratch := { s4.scratch with otfs_cnt := s4.scratch.otfs_cnt + 1#64 } }
  let s_rfin : FullState :=
    { s with
      core := { s.core with
        num_binary := nb2, wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4,
        arena := s.core.arena.set (cref.setWidth 64).toNat
          (s.core.arena[(cref.setWidth 64).toNat]'hcr0_s ||| 0x00080000#32),
        arena_garbage := s.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 }
      scratch := { s.scratch with wsort := wso2, otfs_cnt := s.scratch.otfs_cnt + 1#64 } }
  have hhar : s4.core.arena = s.core.arena := by rw [hs4_base]
  have har_set_eq : s4.core.arena.set (cref.setWidth 64).toNat
      (s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32) =
      s.core.arena.set (cref.setWidth 64).toNat
      (s.core.arena[(cref.setWidth 64).toNat]'hcr0_s ||| 0x00080000#32) := by
    have hval : s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd =
        s.core.arena[(cref.setWidth 64).toNat]'hcr0_s := otfs_list_getElem_of_list_idx hhar rfl
    rw [hval, hhar]
  have hfin_c : s_lfin.core = s_rfin.core := by
    dsimp only [s_lfin, s_rfin]; rw [har_set_eq, hs4_base]
  have hfin_sc : s_lfin.scratch = s_rfin.scratch := by
    dsimp only [s_lfin, s_rfin]; rw [hs4_sc']
  refine otfs_bin_mark_fin hw hnd hcref hng hiu_cut hiu_te ht_u hr_u hlev_u
    hf0_m hf1_m hf0_u hf1_u hf0_lt hf1_lt hent_f har_len h2cv_lt hcr0_s
    (by rw [← hs4_base, ← hs4_sc']; exact hlen4')
    (by rw [← hs4_base]; exact hw4)
    (fullMem_of_eq (by assumption) hfin_c hfin_sc) hQ

private theorem otfs_bin_lits_nodup {s : FullState} {cref : BitVec 32}
    (hnd : FullArenaVarsNodup s) (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    {old_sz : Nat} (h_old_sz : old_sz = fullArenaClauseSizeCore s.core cref.toNat)
    (hsz_lt_ar : cref.toNat + 3 + old_sz ≤ s.core.arena.length) :
    ∀ (j1 j2 : Nat) (h1 : j1 < old_sz) (h2 : j2 < old_sz), j1 ≠ j2 →
      s.core.arena[cref.toNat + 3 + j1]'(by omega) ≠
      s.core.arena[cref.toNat + 3 + j2]'(by omega) := by
  intro j1 j2 h1 h2 hne heq
  have hndc := hnd cref.toNat hcref hng
  let raw := (s.core.arena.drop (cref.toNat + 3)).take old_sz
  have hraw_len : raw.length = old_sz := by
    simp [raw, List.length_take, List.length_drop]; omega
  have hnd_raw : (raw.map fun l : BitVec 32 => l.toNat / 2).Nodup := by
    simpa [fullArenaClauseLits, fullArenaClauseLitsCore, h_old_sz, raw, List.map_map,
      Function.comp_def] using hndc
  have hraw_eq : ∀ j (hj : j < old_sz),
      raw[j]'(hraw_len ▸ hj) = s.core.arena[cref.toNat + 3 + j]'(by omega) :=
    fun j hj => by simp [raw, List.getElem_take, List.getElem_drop]
  exact hne (nodup_map_getElem_inj (fun l : BitVec 32 => l.toNat / 2)
    (hraw_len ▸ h1) (hraw_len ▸ h2) hnd_raw (by rw [hraw_eq j1 h1, hraw_eq j2 h2, heq]))

private theorem otfs_bin_push_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k_in k_out : FullCoreState} {wvec' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' : BitVec 64} {ok : Bool} {lit b : BitVec 32} {ol : Nat}
    (hdm : k_in.dense_mode = 0#64) (hw_in : FullWitnessCutInv c F0 F_cur cut k_in)
    (hk_out : k_out = { k_in with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hlit_lt : lit.toNat < 2 * k_in.cur_vars) (hol_lt : ol < 2 * k_in.cur_vars)
    (hlay' : WatchStackLayout { k_in with wvec := wvec', wstk := wstk', wlen := wlen',
                                          wusable := wu' })
    (hother : ∀ l < 2 * k_in.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore { k_in with wvec := wvec' } l = fullWatchSizeCore k_in l ∧
      ∀ idx < fullWatchSizeCore k_in l,
        wstk'[fullWatchOffCore { k_in with wvec := wvec' } l + idx]? =
          k_in.wstk[fullWatchOffCore k_in l + idx]?)
    (hb_p : b ≠ 0xFFFFFFFF#32 ∧ (b &&& 0x80000000#32) ≠ 0#32 ∧
      (b &&& 0x7FFFFFFF#32).toNat = ol)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ol]))
    (hok_t : ok = true → lit.toNat < 2 * k_in.cur_vars ∧ (1 = 1 ∨ 1 = 2) ∧
      fullWatchSizeCore { k_in with wvec := wvec' } lit.toNat =
        fullWatchSizeCore k_in lit.toNat + 1 ∧
      (∀ k < fullWatchSizeCore k_in lit.toNat,
        wstk'[fullWatchOffCore { k_in with wvec := wvec' } lit.toNat + k]? =
          k_in.wstk[fullWatchOffCore k_in lit.toNat + k]?) ∧
      wstk'[fullWatchOffCore { k_in with wvec := wvec' } lit.toNat +
        fullWatchSizeCore k_in lit.toNat]? = some b ∧ True)
    (hok_f : ok = false →
      (lit.toNat < 2 * k_in.cur_vars →
        fullWatchSizeCore { k_in with wvec := wvec' } lit.toNat =
          fullWatchSizeCore k_in lit.toNat ∧
        ∀ k < fullWatchSizeCore k_in lit.toNat,
          wstk'[fullWatchOffCore { k_in with wvec := wvec' } lit.toNat + k]? =
            k_in.wstk[fullWatchOffCore k_in lit.toNat + k]?) ∧ True) :
    FullWitnessCutInv c F0 F_cur cut k_out := by
  subst hk_out
  refine fcut_with_watches hw_in ?_
  by_cases hok : ok = true
  · obtain ⟨_, _, hsz, hsame, hw0, _⟩ := hok_t hok
    exact fa_watchPush_bin_preserves hdm hw_in.watches hlit_lt hlay' hother hsz hsame hw0
      hb_p.2.1 hb_p.1 (by rw [hb_p.2.2]; exact hol_lt) (by rw [hb_p.2.2]; exact hent)
  · obtain ⟨hsame_f, _⟩ := hok_f (Bool.eq_false_iff.mpr hok)
    exact fa_watchPush_fail_preserves hdm hw_in.watches hlay' fun l hl =>
      if hle : l = lit.toNat then by subst l; exact hsame_f hlit_lt else hother l hl hle

private theorem otfs_bin_sz_lits_info {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} {cref : BitVec 32} (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false) (old_sz : Nat)
    (h_old_sz : old_sz = fullArenaClauseSizeCore s.core cref.toNat) :
    cref.toNat + 3 + old_sz ≤ s.core.arena.length ∧
    cref.toNat + 2 < s.core.arena.length ∧
    (∀ hbd2 : cref.toNat + 2 < s.core.arena.length,
      s.core.arena[cref.toNat + 2]'hbd2 = BitVec.ofNat 32 old_sz) ∧
    (∀ j (_hj : j < old_sz) (hbj : cref.toNat + 3 + j < s.core.arena.length),
      let ot := s.core.arena[cref.toNat + 3 + j]'hbj
      ot.toNat ∈ fullArenaClauseLits s cref.toNat ∧ ot.toNat < 2 * s.core.cur_vars ∧
      ot ≠ 0xFFFFFFFF#32) := by
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hcv_le := hlen.core_ok.cur_vars_le; have hmaxv := c.hmaxv
  unfold dimacsBound at hmaxv
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  refine ⟨by rw [h_old_sz]; omega, by omega, fun hbd2 => ?_, fun j hj hbj => ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have hlt32 : old_sz < 2 ^ 32 := by
      rw [h_old_sz]; exact (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt
    rw [bv32_ofNat_toNat hlt32, h_old_sz]
    have hg : s.core.arena[cref.toNat + 2]? = some (s.core.arena[cref.toNat + 2]'hbd2) :=
      List.getElem?_eq_getElem hbd2
    unfold fullArenaClauseSizeCore; rw [hg, Option.getD_some]
  · have hmem : (s.core.arena[cref.toNat + 3 + j]'hbj).toNat ∈
        fullArenaClauseLitsCore s.core cref.toNat :=
      (mem_fullArenaClauseLitsCore_iff (by rw [← h_old_sz]; omega)).mpr ⟨j, h_old_sz ▸ hj, rfl⟩
    have hlt := hw.arena.lits_lt cref.toNat hcref hng _ hmem
    exact ⟨hmem, hlt, bv32_lit_neq_ff (by omega)⟩

private def otfs_bin_scan_expr (ar_ptr lvl_ptr : BitVec 64) (cref uip sz_v : BitVec 32)
    (J : Cont [i32, i32, i32]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32]])
    (fun Js_1 =>
      Blocks.cons
        (fun p =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool) (Arg.var p.snd.fst, Arg.var sz_v, ()))
            fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun p_2 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.fst, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ar_ptr, Arg.var p_6.fst, ())) fun p_7 =>
            Expr.load i32 (Arg.var p_7.fst) fun ld =>
            Expr.group (sig := [[i32, i32]])
              (fun Js =>
                Blocks.cons
                  (fun p_8 =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                      fun p =>
                    Expr.jump Js_1.fst (Arg.var p_8.fst, Arg.var p.fst, ()))
                  Blocks.nil)
              fun Js_2 =>
              Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool) (Arg.var ld, Arg.var uip, ())) fun p_8 =>
              Expr.jnz (Arg.var p_8.fst)
                (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun p_9 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_9.fst, ())) fun p_10 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_10.fst, Arg.imm 4, ())) fun p_11 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var lvl_ptr, Arg.var p_11.fst, ()))
                  fun p_12 =>
                Expr.load i32 (Arg.var p_12.fst) fun ld_1 =>
                Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool) (Arg.var ld_1, Arg.imm 0, ()))
                  fun p_13 =>
                Expr.jnz (Arg.var p_13.fst)
                  (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool)
                      (Arg.var p.fst, Arg.imm 4294967295, ())) fun p_14 =>
                  Expr.jnz (Arg.var p_14.fst)
                    (Expr.jump Js_2.fst (Arg.var ld, Arg.imm 4294967295, ()))
                    (Expr.jump J (Arg.var p.fst, Arg.var ld, Arg.var p.snd.fst, ())))
                  (Expr.jump Js_2.fst (Arg.var p.fst, Arg.imm 4294967295, ())))
                (Expr.jump Js_2.fst (Arg.var p.fst, Arg.imm 4294967295, ())))
            (Expr.jump J (Arg.var p.fst, Arg.imm 4294967295, Arg.var p.snd.fst, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 4294967295, Arg.imm 0, ())

private theorem otfs_bin_scan_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {cref uip sz_v : BitVec 32} {old_sz : Nat}
    (hsz_v : sz_v.toNat = old_sz) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hsz_lt_ar : cref.toNat + 3 + old_sz ≤ s.core.arena.length)
    (P_lit : BitVec 32 → Prop)
    (hlits_info : ∀ (j : Nat) (_ : j < old_sz),
      let ot := s.core.arena[cref.toNat + 3 + j]'(by omega)
      P_lit ot ∧ ot.toNat < 2 * s.core.cur_vars ∧ ot ≠ 0xFFFFFFFF#32)
    (hnodup_j : ∀ (j1 j2 : Nat) (_ : j1 < old_sz) (_ : j2 < old_sz), j1 ≠ j2 →
      s.core.arena[cref.toNat + 3 + j1]'(by omega) ≠
        s.core.arena[cref.toNat + 3 + j2]'(by omega))
    {J : Cont [i32, i32, i32]}
    (hJ_none : ∀ f0 iv, J (f0, 0xFFFFFFFF#32, iv, ()) m)
    (hJ_found : ∀ (i j : Nat), j < i → i < old_sz →
      let f0 := s.core.arena[cref.toNat + 3 + j]?.getD 0#32
      let f1 := s.core.arena[cref.toNat + 3 + i]?.getD 0#32
      P_lit f0 → P_lit f1 → f0 ≠ uip → f1 ≠ uip → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      J (f0, f1, BitVec.ofNat 32 i, ()) m) :
    wp Γ Q X (otfs_bin_scan_expr c.pArena c.pLevel cref uip sz_v J) m := by
  have hcref_bd : cref.toNat + 3 + old_sz < 2 ^ 61 := by
    have hlen_ar := hlen.core_ok.arena_len_arr
    have hcap := c.harena
    simp only [LeanQbe.T.Examples.Kissat.Ref.dimacsBound] at hcap
    omega
  have h_old_32 : old_sz < 2 ^ 32 := by omega
  dsimp only [otfs_bin_scan_expr]
  c0_hsteps_nogrp
  refine wp_loop_group (fun r (f0, iv, ()) ml => ∃ i : Nat,
    ml = m ∧ r = old_sz - i ∧ i ≤ old_sz ∧ iv = BitVec.ofNat 32 i ∧
    (f0 = 0xFFFFFFFF#32 ∨ ∃ j < i,
      f0 = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
      f0 ≠ uip ∧ 0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
  · rintro L r ⟨f0, iv, ⟨⟩⟩ ml ih ⟨i, rfl, rfl, hile, rfl, hf0⟩
    c0_hsteps_nogrp
    · have hilt : i < old_sz := by
        have hb : (BitVec.ofNat 32 i).toNat < sz_v.toNat := ‹_›
        rw [bv32_ofNat_toNat (by omega)] at hb
        rwa [hsz_v] at hb
      obtain ⟨hot_mem, hot_lt, _hot_ff⟩ := hlits_info i hilt
      let ot := s.core.arena[cref.toNat + 3 + i]'(by omega)
      have hot_get : ot = s.core.arena[cref.toNat + 3 + i]?.getD 0#32 := by
        dsimp only [ot]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hcr_i_z : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat =
          cref.toNat + 3 + i := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
          zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
        simp only [BitVec.reduceToNat]; omega
      have hcr_i_bd : (cref.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
          s.core.arena.length := by rw [hcr_i_z]; omega
      have hot_idx_eq : s.core.arena[(cref.setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd = ot := getElem_eq_of_idx hcr_i_z
      have hot_lvl_lt : (s.core.arena[(cref.setWidth 64 + 3 +
          (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd).toNat / 2 < s.core.cur_vars := by
        rw [hot_idx_eq]; exact Nat.div_lt_of_lt_mul hot_lt
      have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64 =
          cref.toNat + 3 + i := by
        simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
      have hot_c0_eq : s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
          i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega) = ot := getElem_eq_of_idx hc_idx
      have hot_lvl_c0 : (s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
          i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat / 2 < s.core.cur_vars := by
        rw [hot_c0_eq]; exact Nat.div_lt_of_lt_mul hot_lt
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, i32]) (fun p ml_post =>
          let f0' := p.1
          ml_post = ml ∧
          (f0' = 0xFFFFFFFF#32 ∨ ∃ j < i + 1,
            f0' = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
            f0' ≠ uip ∧ 0 < (s.core.lvl[f0'.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
      · rintro _ ⟨f0', _f1, ⟨⟩⟩ ml_post ⟨rfl, hf0'⟩; c0_hsteps
        rw [show BitVec.ofNat 32 i + (1 : BitVec 32) = BitVec.ofNat 32 (i + 1) by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
            bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega),
            Nat.mod_eq_of_lt (by omega)]]
        exact ih (old_sz - (i + 1)) _ ml_post (by omega) ⟨i + 1, rfl, rfl, by omega, rfl, hf0'⟩
      · intro J2 hJ2; c0_hsteps
        · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
            rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
          have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
            exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
              (getElem_eq_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                (getElem_eq_of_idx hc_idx))))
          have hot_ne_uip : ot ≠ uip := fun he =>
            ‹¬ _ = uip› ((getElem_eq_of_idx hc_idx).trans he)
          have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
              (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := getElem_eq_of_idx hcr_i_z
          rw [h_ot_g]
          exact hJ2 (ot, 0xFFFFFFFF#32, ()) ml
            ⟨rfl, Or.inr ⟨i, Nat.lt_succ_self i, hot_get, hot_ne_uip, hpos_ot⟩⟩
        · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
            rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
          have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
            exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
              (getElem_eq_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                (getElem_eq_of_idx hc_idx))))
          have hot_ne_uip : ot ≠ uip := fun he =>
            ‹¬ _ = uip› ((getElem_eq_of_idx hc_idx).trans he)
          have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
              (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := getElem_eq_of_idx hcr_i_z
          rcases hf0 with rfl | ⟨j, hj, rfl, hju, hjl⟩
          · exfalso; exact ‹¬ (0xFFFFFFFF#32 = 0xFFFFFFFF#32)› rfl
          · have hj_get : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 =
                s.core.arena[cref.toNat + 3 + j]'(by omega) := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hf_ne : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ ot := by
              rw [hj_get]; exact hnodup_j j i (by omega) hilt (by omega)
            have hj_info := hlits_info j (by omega); rw [← hj_get] at hj_info
            have hot_mem' : P_lit (s.core.arena[cref.toNat + 3 + i]?.getD 0#32) :=
              hot_get ▸ hot_mem
            rw [h_ot_g, hot_get] at *
            exact hJ_found i j hj hilt hj_info.1 hot_mem' hju hot_ne_uip hf_ne hjl hpos_ot
        · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
        · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
    · c0_hsteps; exact hJ_none _ _
  · intro L hL; c0_hsteps
    exact hL old_sz (0xFFFFFFFF#32, 0#32, ()) m
      ⟨0, rfl, rfl, Nat.zero_le _, rfl, Or.inl rfl⟩

/-- Canonical `Func.wp` proof for `full_otfs_bin` (`Spec.fullOtfsBinSpec`). -/
theorem full_otfs_bin_wp (Γ : Env)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hUnw : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hPush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ args m Q X, Spec.fullOtfsBinSpec args m Q X →
      Func.wp Γ full_otfs_bin_body args m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw, hnd, hdm, hcref, hng, huip_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw.cut_le
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have hcv_le := hlen.core_ok.cur_vars_le; have hmaxv := c.hmaxv; have harena := c.harena
  have hwcap := c.hwcap; unfold dimacsBound at hmaxv harena hwcap
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hwvec_len := hlen.core_ok.wvec_len; have hwstk_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  obtain ⟨old_sz, h_old_sz⟩ : ∃ n, n = fullArenaClauseSizeCore s.core cref.toNat := ⟨_, rfl⟩
  obtain ⟨hsz_lt_ar, hcref_bd, hsz_get_fn, hlits_info_fn⟩ :=
    otfs_bin_sz_lits_info hlen hw hcref hng old_sz h_old_sz
  have hsz_get : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz :=
    hsz_get_fn (by omega)
  have hlits_info : ∀ j (hj : j < old_sz),
      let ot := s.core.arena[cref.toNat + 3 + j]'(by omega)
      ot.toNat ∈ fullArenaClauseLits s cref.toNat ∧ ot.toNat < 2 * s.core.cur_vars ∧
      ot ≠ 0xFFFFFFFF#32 := fun j hj => hlits_info_fn j hj (by omega)
  have hnodup_j := otfs_bin_lits_nodup hnd hcref hng h_old_sz hsz_lt_ar
  have hret_same : Q (false, ()) m :=
    hQ false s.core.arena s.core.arena_garbage s.core.wvec s.core.wstk s.core.wlen s.core.wusable
      s.core.num_binary s.core.confl_type s.core.confl_ref s.core.confl_lit0 s.core.confl_lit1
      s.core.oom s.scratch m hlen (fcut_shrink_cut hw (Nat.le_of_lt hiu_cut)) hnd
      ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm
  unfold Func.wp full_otfs_bin_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32, i32, i32]) (fun p ml =>
      let f0 := p.1; let f1 := p.2.1
      ml = m ∧ ((f0 = 0xFFFFFFFF#32 ∨ f1 = 0xFFFFFFFF#32) ∨
        (f0.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f1.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f0 ≠ uip ∧ f1 ≠ uip ∧ f0 ≠ f1 ∧
         0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat ∧
         0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat))) ?_ ?_
  · rintro _ ⟨f0, f1, _iv, ⟨⟩⟩ ml ⟨hml, hpost⟩
    subst ml; dsimp only at hpost
    rcases hpost with hf_eq | ⟨hf0_m, hf1_m, hf0_u, hf1_u, hf_ne, hl0_pos, hl1_pos⟩
    · c0_let_simp; refine wp_jnz_of (fun _ => hret_same) (fun hne0 => ?_)
      c0_let_simp; refine wp_jnz_of (fun _ => hret_same) (fun hne1 => ?_)
      rcases hf_eq with h0 | h1
      · exact absurd h0 (by simpa using hne0)
      · exact absurd h1 (by simpa using hne1)
    · have hf0_lt : f0.toNat < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng _ hf0_m
      have hf1_lt : f1.toNat < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng _ hf1_m
      have hf0_31 : f0.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf0_lt h2cv_lt
      have hf1_31 : f1.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf1_lt h2cv_lt
      have hf0_ff : f0 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf0_31
      have hf1_ff : f1 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf1_31
      have hf0_2l1 : ((f0.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
          2 * f0.toNat + 1 := by
        rw [otfs_bv64_shl_sext1_add1 _ (by rw [zext_toNat f0 (by decide)]; omega),
          zext_toNat f0 (by decide)]
      have hf1_2l1 : ((f1.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
          2 * f1.toNat + 1 := by
        rw [otfs_bv64_shl_sext1_add1 _ (by rw [zext_toNat f1 (by decide)]; omega),
          zext_toNat f1 (by decide)]
      have hf0_bd1 : ((f0.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
          s.core.wvec.length := by rw [hf0_2l1, hwvec_len]; omega
      have hf1_bd1 : ((f1.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
          s.core.wvec.length := by rw [hf1_2l1, hwvec_len]; omega
      have hlay0 : WatchStackLayout s.core := by
        have h := hw.watches; unfold ModeWatchesInv at h; rw [ite_eq_left hdm] at h; exact h.layout
      have hmw0 : WatchesInv F_cur s.core := by
        have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_left hdm] at h
      c0_hsteps_nogrp
      · refine wp_join_group (ts := [i32]) (fun (src, ()) ml =>
            ml = m ∧ (src = f0 ∨ src = f1)) ?_ ?_
        · rintro _ ⟨src, ⟨⟩⟩ ml ⟨hml_s, hsrc_or⟩; subst ml
          have hsrc_lt : src.toNat < 2 * s.core.cur_vars :=
            hsrc_or.elim (fun h => h ▸ hf0_lt) (fun h => h ▸ hf1_lt)
          have hsrc_2l : (src.setWidth 64 <<< BitVec.signExtend 64 1#32).toNat =
              2 * src.toNat := by
            rw [otfs_bv64_shl_sext1 _ (by rw [zext_toNat src (by decide)]; omega),
              zext_toNat src (by decide)]
          have hsrc_2l1 : ((src.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
              2 * src.toNat + 1 := by
            rw [otfs_bv64_shl_sext1_add1 _ (by rw [zext_toNat src (by decide)]; omega),
              zext_toNat src (by decide)]
          have hsrc_bd0 : (src.setWidth 64 <<< BitVec.signExtend 64 1#32).toNat <
              s.core.wvec.length := by rw [hsrc_2l, hwvec_len]; omega
          have hsrc_bd1 : ((src.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
              s.core.wvec.length := by rw [hsrc_2l1, hwvec_len]; omega
          refine wp_join_group (ts := [i32]) (fun (tgt, ()) ml =>
              ml = m ∧ (tgt = f0 ∨ tgt = f1)) ?_ ?_
          · rintro _ ⟨tgt, ⟨⟩⟩ ml ⟨hml_t, _htgt⟩; subst ml
            c0_hsteps_nogrp
            let off_s := fullWatchOffCore s.core src.toNat
            let sz_s := fullWatchSizeCore s.core src.toNat
            let pend_s := off_s + sz_s
            have hbnd_s := hlay0.bounds src.toNat hsrc_lt
            have hoff_eq : (s.core.wvec[(src.setWidth 64 <<< BitVec.signExtend 64
                1#32).toNat]'hsrc_bd0).toNat = off_s := by
              unfold off_s fullWatchOffCore
              rw [List.getElem?_eq_getElem (by rw [hwvec_len]; omega), Option.getD_some]
              exact congrArg BitVec.toNat (getElem_eq_of_idx hsrc_2l)
            have hsz_eq : (s.core.wvec[((src.setWidth 64 <<< BitVec.signExtend 64
                1#32) + 1#64).toNat]'hsrc_bd1).toNat = sz_s := by
              unfold sz_s fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by rw [hwvec_len]; omega), Option.getD_some]
              exact congrArg BitVec.toNat (getElem_eq_of_idx hsrc_2l1)
            have hoff64 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                BitVec.signExtend 64 1#32).toNat]'hsrc_bd0)).toNat = off_s := by
              rw [zext_toNat _ (by decide), hoff_eq]
            have hsz64 : (BitVec.setWidth 64 (s.core.wvec[((src.setWidth 64 <<<
                BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1)).toNat = sz_s := by
              rw [zext_toNat _ (by decide), hsz_eq]
            have hpend64 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                  BitVec.signExtend 64 1#32).toNat]'hsrc_bd0) +
                BitVec.setWidth 64 (s.core.wvec[((src.setWidth 64 <<<
                  BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1)).toNat = pend_s := by
              rw [BitVec.toNat_add, hoff64, hsz64]; exact Nat.mod_eq_of_lt (by omega)
            refine wp_join_group (ts := [.bool, i64])
                (fun (_res, _p, ()) ml => ml = m) ?_ ?_
            · rintro _ ⟨has_bin, _pfin, ⟨⟩⟩ ml hml_hb; subst ml
              c0_hsteps_nogrp
              have hent_f := hent f0 f1 hf0_m hf1_m hf0_u hf1_u hf_ne hl0_pos hl1_pos
              refine wp_join_group (ts := []) (fun _ ml => ∃ s2 : FullState,
                ∃ (wv2 ws2 : List (BitVec 32)) (wl2 : Nat) (wu2 nb2 : BitVec 64)
                  (wso2 : List (BitVec 32)),
                  s2.core = { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                          wusable := wu2, num_binary := nb2 } ∧
                  s2.scratch = { s.scratch with wsort := wso2 } ∧
                  s2.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s2.core ∧
                  (FullMem c s2 ⋆ R) ml) ?_ ?_
              · rintro _ ⟨⟩ ml ⟨s2, wv2, ws2, wl2, wu2, nb2, wso2, hs2_c, hs2_sc, hlen2, hw2, hm2⟩
                exact otfs_bin_tail_wp hNext hUnw hw hnd hdm hcref hng hiu_cut hiu_te ht_u
                  hr_u hlev_u hf0_m hf1_m hf0_u hf1_u hf0_lt hf1_lt hent_f har_len h2cv_lt
                  hs2_c hs2_sc hlen2 hw2 hm2 hQ
              · intro Jw hJw
                c0_hsteps_nogrp
                · exact hJw () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
                    s.core.num_binary, s.scratch.wsort, rfl, rfl, hlen, hw, hm⟩
                · refine wp_join_group (ts := []) (fun _ ml_d =>
                    ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat)
                      (wu_d : BitVec 64) (wso_d : List (BitVec 32)),
                      s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d,
                                               wusable := wu_d } ∧
                      s_d.scratch = { s.scratch with wsort := wso_d } ∧
                      s_d.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s_d.core ∧
                      (FullMem c s_d ⋆ R) ml_d) ?_ ?_
                  · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                      hlen_d, hw_d, hm_d⟩
                    clear hm
                    have hb0_p := bin_rsn_mask_props (l := f1) hf1_31
                    have hb1_p := bin_rsn_mask_props (l := f0) hf0_31
                    let b0 := (f1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                    let b1 := (f0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                    have hent_sym :
                        (cnfOfClauses F_cur).EntailsClause (cnfClause [f1.toNat, f0.toNat]) :=
                      entails_of_mem_or_false hent_f fun l hl => by
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                        exact Or.inl (by rcases hl with rfl | rfl <;> simp)
                    have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm
                    have hlay_d : WatchStackLayout s_d.core := by
                      have h := hw_d.watches; unfold ModeWatchesInv at h
                      rw [ite_eq_left hsd_dm] at h; exact h.layout
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ ml_o =>
                      ∃ (wv_o ws_o : List (BitVec 32)) (wl_o : Nat)
                        (wu_o : BitVec 64) (wso_o : List (BitVec 32)),
                        let s_o : FullState :=
                          { s with
                            core := { s.core with wvec := wv_o, wstk := ws_o, wlen := wl_o,
                                                  wusable := wu_o }
                            scratch := { s.scratch with wsort := wso_o } }
                        s_o.LengthsOk c ∧
                        FullWitnessCutInv c F0 F_cur cut s_o.core ∧
                        (FullMem c s_o ⋆ R) ml_o)
                      (fun _ ⟨⟩ ml_o ⟨wv_o, ws_o, wl_o, wu_o, wso_o, hlen_o, hw_o, hm_o⟩ => by
                        c0_hsteps
                        exact otfs_bin_oom_exit (wv := wv_o) (ws := ws_o) (wl := wl_o)
                          (wu := wu_o) (wso := wso_o) hiu_cut hnd hlen_o hw_o
                          (by assumption) hQ) ?_
                    intro J_oom hJoom
                    c0_call hPush
                    refine ⟨c, s_d, R, rfl, hlen_d, hlay_d,
                      (fun _ => hb0_p.1), (fun hk => by cases hk), hm_d,
                      fun ok1 wv1 ws1 wl1 wu1 wso1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1 => ?_⟩
                    clear hm_d
                    let s1 : FullState :=
                      { s_d with
                        core := { s_d.core with wvec := wv1, wstk := ws1, wlen := wl1,
                                                wusable := wu1 }
                        scratch := { s_d.scratch with wsort := wso1 } }
                    have hs1_c : s1.core = { s.core with
                        wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 } := by
                      dsimp only [s1]; rw [hsd_c]
                    have hs1_sc : s1.scratch = { s.scratch with wsort := wso1 } := by
                      dsimp only [s1]; rw [hsd_sc]
                    have hw1 : FullWitnessCutInv c F0 F_cur cut s1.core :=
                      otfs_bin_push_witness hsd_dm hw_d rfl
                        (by rw [hsd_c]; exact hf0_lt) (by rw [hsd_c]; exact hf1_lt) hlay1 hother1
                        hb0_p hent_f (fun h => by
                          obtain ⟨a, _, c1, d1, e1, _⟩ := hok1t h
                          exact ⟨a, Or.inl rfl, c1, d1, e1, trivial⟩)
                        (fun h => ⟨(hok1f h).1, trivial⟩)
                    have hs1_dm : s1.core.dense_mode = 0#64 := by rw [hs1_c]; exact hdm
                    by_cases hok1 : ok1 = true
                    · subst hok1; clear hok1t hok1f
                      c0_hsteps_nogrp
                      · c0_call hPush
                        refine ⟨c, s1, R, rfl, hlen1, hlay1,
                          (fun _ => hb1_p.1), (fun hk => by cases hk), hm1,
                          fun ok2 wv2 ws2 wl2 wu2 wso2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2 => ?_⟩
                        clear hm1
                        let s2 : FullState :=
                          { s1 with
                            core := { s1.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                                   wusable := wu2 }
                            scratch := { s1.scratch with wsort := wso2 } }
                        have hs2_c : s2.core = { s.core with
                            wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 } := by
                          dsimp only [s2]; rw [hs1_c]
                        have hs2_sc : s2.scratch = { s.scratch with wsort := wso2 } := by
                          dsimp only [s2]; rw [hs1_sc]
                        have hw2 : FullWitnessCutInv c F0 F_cur cut s2.core :=
                          otfs_bin_push_witness hs1_dm hw1 rfl
                            (by rw [hs1_c]; exact hf1_lt) (by rw [hs1_c]; exact hf0_lt)
                            hlay2 hother2 hb1_p hent_sym (fun h => by
                              obtain ⟨a, _, c1, d1, e1, _⟩ := hok2t h
                              exact ⟨a, Or.inl rfl, c1, d1, e1, trivial⟩)
                            (fun h => ⟨(hok2f h).1, trivial⟩)
                        by_cases hok2 : ok2 = true
                        · subst hok2; c0_hsteps
                          · let s2_nb : FullState :=
                              { s2 with
                                core := { s2.core with num_binary := s2.core.num_binary + 1#64 } }
                            have hnb_c : s2_nb.core = { s.core with
                                wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2,
                                num_binary := s.core.num_binary + 1#64 } := by
                              dsimp only [s2_nb]; rw [hs2_c]
                            have hnb_hw : FullWitnessCutInv c F0 F_cur cut s2_nb.core :=
                              ⟨{ hw2.toFullOtfsWitnessInv with
                                  arena := { hw2.arena with len_ok := hw2.arena.len_ok }
                                  watches := hw2.watches.with_wstk rfl rfl rfl rfl rfl
                                    (fun _ hr => hr) },
                                hw2.cut_le, hw2.reason_inv_cut, hw2.reason_lit_mem_cut⟩
                            exact hJw () _
                              ⟨s2_nb, wv2, ws2, wl2, wu2, s.core.num_binary + 1#64, wso2,
                              hnb_c, hs2_sc, ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩,
                              hnb_hw, by assumption⟩
                          · exact absurd (by assumption : true = false) (by decide)
                        · have hok2f : ok2 = false := Bool.eq_false_iff.mpr hok2
                          subst hok2f; c0_hsteps
                          exact hJoom () _ ⟨wv2, ws2, wl2, wu2, wso2,
                            by rw [← hs2_c, ← hs2_sc]; exact hlen2,
                            hs2_c ▸ hw2, fullMem_of_eq hm2 hs2_c hs2_sc⟩
                      · exact absurd (by assumption : true = false) (by decide)
                    · have hok1f : ok1 = false := Bool.eq_false_iff.mpr hok1
                      subst hok1f; c0_hsteps
                      exact hJoom () _ ⟨wv1, ws1, wl1, wu1, wso1,
                        by rw [← hs1_c, ← hs1_sc]; exact hlen1,
                        hs1_c ▸ hw1, fullMem_of_eq hm1 hs1_c hs1_sc⟩
                  · intro Jd hJd
                    exact otfs_wstack_ensure2_ret_false_wp hDefrag hlen hdm hw.watches hm
                      (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o =>
                        otfs_bin_oom_exit (wv := wv_i) (ws := ws_i) (wl := wl_i) (wu := wu_i)
                          (wso := wso_i) hiu_cut hnd
                          ⟨by have h := hlen_i.core_ok; rw [hsi_c] at h; exact h,
                           by have h := hlen_i.scratch_ok; rw [hsi_sc] at h; exact h⟩
                          (by rw [hsi_c] at hmw_i; exact fcut_with_watches hw hmw_i)
                          (fullMem_of_eq hm_o (by dsimp only; rw [hsi_c])
                            (by dsimp only; exact hsi_sc))
                          hQ)
                      (fun xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                          hlen_d, hmw_d, hm_d⟩ =>
                        hJd xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                          hlen_d, by
                            rw [hsd_c] at hmw_d ⊢; exact fcut_with_watches hw hmw_d, hm_d⟩)
            · intro Jb hJb
              refine wp_loop_group (fun r (pv, ()) ml =>
                  ml = m ∧ r = pend_s - pv.toNat ∧
                  off_s ≤ pv.toNat ∧ pv.toNat ≤ pend_s ∧
                  WatchSliceOk F_cur s.core src.toNat pv.toNat (pend_s - pv.toNat)) ?_ ?_
              · rintro L r ⟨pv, ⟨⟩⟩ ml ih ⟨hml_l, rfl, hlo, hhi, hsl⟩; subst ml
                c0_hsteps_nogrp
                · have hp_lt : pv.toNat < pend_s := by
                    have hbd0' : 2 * src.toNat % 2 ^ 64 < s.core.wvec.length := by
                      rw [Nat.mod_eq_of_lt (by omega), hwvec_len]; omega
                    have hbd1' : (2 * src.toNat + 1) % 2 ^ 64 < s.core.wvec.length := by
                      rw [Nat.mod_eq_of_lt (by omega), hwvec_len]; omega
                    have hc0 : pv.toNat < (s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0').toNat +
                        (s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1').toNat :=
                      Nat.lt_of_lt_of_le (‹pv.toNat < _› : pv.toNat <
                        ((s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0').toNat +
                          (s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1').toNat) % 2 ^ 64)
                        (Nat.mod_le _ _)
                    have he0 : s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0' =
                        s.core.wvec[(src.setWidth 64 <<<
                          BitVec.signExtend 64 1#32).toNat]'hsrc_bd0 :=
                      getElem_eq_of_idx (by rw [hsrc_2l, Nat.mod_eq_of_lt (by omega)])
                    have he1 : s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1' =
                        s.core.wvec[((src.setWidth 64 <<<
                          BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1 :=
                      getElem_eq_of_idx (by rw [hsrc_2l1, Nat.mod_eq_of_lt (by omega)])
                    rw [he0, he1, hoff_eq, hsz_eq] at hc0; exact hc0
                  have hpw : pv.toNat < s.core.wstk.length := by rw [hwstk_len]; omega
                  let w0 := s.core.wstk[pv.toNat]'hpw
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [.bool, i64])
                      (fun (br, pv', ()) ml' =>
                        ml' = m ∧ br = false ∧ pend_s - pv'.toNat < pend_s - pv.toNat ∧
                        off_s ≤ pv'.toNat ∧ pv'.toNat ≤ pend_s ∧
                        WatchSliceOk F_cur s.core src.toNat pv'.toNat (pend_s - pv'.toNat)) ?_ ?_
                  · rintro _ ⟨br, pv', ⟨⟩⟩ ml' ⟨hml', hbr, hdec', hlo', hhi', hsl'⟩
                    subst ml'; subst br; c0_hsteps
                    exact ih (pend_s - pv'.toNat) (pv', ()) m hdec' ⟨rfl, rfl, hlo', hhi', hsl'⟩
                  · intro J_s hJs; c0_hsteps
                    · exact hJb (true, pv, ()) m rfl
                    · have hfl : (w0 &&& 0x80000000#32) ≠ 0#32 := by assumption
                      rcases otfs_bin_watchSlice_tail hsl (by omega) with
                        ⟨w', hw', _, _, _, _, hrest⟩ | ⟨_, w', _, hw', _, hfl0, _, _, _⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'; subst w'
                        have hp1 : (pv + 1#64).toNat = pv.toNat + 1 :=
                          otfs_bv64_add1_nat pv (by omega)
                        exact hJs (false, pv + 1#64, ()) m ⟨rfl, rfl, by rw [hp1]; omega,
                          by rw [hp1]; omega, by rw [hp1]; omega, by rw [hp1, show pend_s -
                            (pv.toNat + 1) = pend_s - pv.toNat - 1 by omega]; exact hrest⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'
                        subst w'; exact absurd hfl0 hfl
                    · have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by assumption
                      rcases otfs_bin_watchSlice_tail hsl (by omega) with
                        ⟨w', hw', hfl, _⟩ | ⟨h2le, w', _, hw', _, _, _, _, hrest⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'
                        subst w'; exact absurd hfl0 hfl
                      · have hp2 : (pv + 2#64).toNat = pv.toNat + 2 := by
                          rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                          exact Nat.mod_eq_of_lt (by omega)
                        exact hJs (false, pv + 2#64, ()) m ⟨rfl, rfl, by rw [hp2]; omega,
                          by rw [hp2]; omega, by rw [hp2]; omega, by rw [hp2, show pend_s -
                            (pv.toNat + 2) = pend_s - pv.toNat - 2 by omega]; exact hrest⟩
                · c0_hsteps; exact hJb (false, pv, ()) m rfl
              · intro L hL; c0_hsteps
                have hshl1_n : (src.setWidth 64 <<< BitVec.signExtend 64 1#32) =
                    src.setWidth 64 <<< (1 : Nat) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [hsrc_2l, bv64_shl1_nat _ (by rw [zext_toNat src (by decide)]; omega),
                    zext_toNat src (by decide)]
                have hsrc_bd0_n : (src.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
                  rw [← hshl1_n]; exact hsrc_bd0
                have hoff64_1 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                    (1 : Nat)).toNat]'hsrc_bd0_n)).toNat = off_s := by
                  simpa only [← hshl1_n] using hoff64
                exact hL sz_s (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                    (1 : Nat)).toNat]'hsrc_bd0_n), ()) m
                  ⟨rfl, by rw [hoff64_1]; unfold pend_s; omega,
                   by rw [hoff64_1]; exact Nat.le_refl _,
                   by rw [hoff64_1]; unfold pend_s; omega,
                   by rw [hoff64_1, show pend_s - off_s = sz_s by unfold pend_s; omega]
                      exact hmw0.slices src.toNat hsrc_lt⟩
          · intro Jt hJt; c0_hsteps
            · exact hJt _ _ ⟨rfl, Or.inr rfl⟩
            · exact hJt _ _ ⟨rfl, Or.inl rfl⟩
        · intro Js hJs; c0_hsteps
          · exact hJs _ _ ⟨rfl, Or.inl rfl⟩
          · exact hJs _ _ ⟨rfl, Or.inr rfl⟩
  · intro J hJ
    have hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
      rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp; omega
    have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_z]; omega
    exact otfs_bin_scan_wp
      (sz_v := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd)
      (by rw [getElem_eq_of_idx (hj := by omega) hcr2_z, hsz_get, bv32_ofNat_toNat (by omega)])
      hlen (by assumption) hcv_le hlvl_len hsz_lt_ar
      (fun l : BitVec 32 => l.toNat ∈ fullArenaClauseLits s cref.toNat)
      hlits_info hnodup_j
      (fun f0 iv => hJ (f0, 0xFFFFFFFF#32, iv, ()) m ⟨rfl, Or.inl (Or.inr rfl)⟩)
      (fun i j hji hilt hp0 hp1 h0u h1u h01 hl0 hl1 =>
        hJ (_, _, BitVec.ofNat 32 i, ()) m
          ⟨rfl, Or.inr ⟨hp0, hp1, h0u, h1u, h01, hl0, hl1⟩⟩)

end LeanQbe.T.Examples.Kissat.Proof.Deduce
