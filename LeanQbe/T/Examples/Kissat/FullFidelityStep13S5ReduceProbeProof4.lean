/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof3b
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_preprocess_m6` Proof (`Proof4`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `<= 100` cols, `<= 390` lines per decl,
`< 1,400` LOC, `0` `@[expose]` on theorems/lemmas) for
`FullFidelityStep13S5ReduceProbe.full_preprocess_m6_body` against `FullM6.fullM6PreprocessSpec`.
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil FullArenaTactics
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Preprocessing State & Callee Helpers -/

private theorem s5_preproc_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private theorem s5_preproc_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb; change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem; unfold fullArenaClauseGarb at hgb; rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private theorem s5_preproc_with_searchTicks {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInv c F0 ext s) (st' : BitVec 64) :
    FullM6HdrInv c F0 ext { s with scratch := { s.scratch with search_ticks := st' } } :=
  let sc_ok := hinv.sparse.1.lengths.scratch_ok
  have hsp : FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := st' } } :=
    ⟨⟨⟨hinv.sparse.1.lengths.core_ok, { sc_ok with walk_vals_len := sc_ok.walk_vals_len }⟩,
        hinv.sparse.1.witness⟩,
      hinv.sparse.2.1, hinv.sparse.2.2.1,
      ⟨hinv.sparse.2.2.2.1.1, hinv.sparse.2.2.2.1.2⟩, hinv.sparse.2.2.2.2⟩
  FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp

private theorem s5_preproc_with_unflushed0 {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInv c F0 ext s) :
    FullM6HdrInv c F0 ext { s with core := { s.core with unflushed := 0#64 } } := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  have hw' := Full.FullDenseWatchHelpers.fullWitnessInv_with_unflushed hw 0#64
  exact FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk
    ⟨⟨⟨{ hinv.sparse.lengths.core_ok with vals_len := hinv.sparse.lengths.core_ok.vals_len },
        hinv.sparse.lengths.scratch_ok⟩, ⟨F_cur, hw'⟩⟩,
      hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1, hinv.sparse.2.2.2.2⟩

private theorem s5_preproc_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hProp : ∀ a m' Q' X', step13BcpM6Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv0 : FullM6HdrInv c F0 ext s0) (hcl0 : s0.core.cur_level = 0)
    (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat) (hm0 : (FullM6HdrMem c ext s0 ⋆ R) m0)
    (hk : ∀ r ext' s' m', FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s0.core.trail_end ≤ s'.core.trail_end →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end) →
      (r = 1#64 → F0.Unsat) → (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" (as := [i64]) (bs := [i64]) args k) m0 := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  obtain ⟨F_cur, hw0⟩ := hinv0.sparse.1.witness
  refine hProp _ _ _ X ⟨c, F0, F_cur, ext, s0, R, rfl, hinv0.cfgOk, hinv0.extOk,
    hinv0.sparse.lengths, hw0, hinv0.sparse.2.2.2.2, hm0, ?_⟩
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' s'
    hext' _ hexti' hw' htr hap hps _ _ _ _ hfu hr h0 h1 _ _ hm'
  have hsp' : FullSparseInv c F0 s' :=
    ⟨⟨hexti', ⟨F_cur, hw'⟩⟩, hinv0.sparse.2.1,
      s5_preproc_arenaVarsNodup_perm hap hinv0.sparse.2.2.1,
      FullExtScratchOk.of_pres hinv0.sparse.2.2.2.1 ⟨hps.1.1, hps.1.2⟩ fun _ hr' => by
        unfold fullArenaClauseRefs at hr' ⊢; rwa [hap.2.1],
      hinv0.sparse.2.2.2.2⟩
  exact hk r ext' s' m' (FullM6HdrInv.mk_inv hinv0.cfgOk hext' hsp') hcl0
    (Nat.le_trans hfu hfu0) htr.1 hr (fun h0eq => (h0 h0eq).1)
    (fun h1eq => s5_preproc_level0_unsat hw' hcl0 (h1 h1eq).2.2) hm'

private abbrev S5PreprocQ (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r c' ext' s' m',
    FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
    (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
    (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem s5_preproc_call_compact {Γ : Env} {c c' : FullCfg} {F0 : CNF Nat}
    {ext' : List (BitVec 64)} {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [i64]} {X : XPost} {k_ok : Expr Val Cont [i64]}
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hcmp : FullCfgCompat c c') (hinv' : FullM6HdrInv c' F0 ext' s')
    (hfu' : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm' : (FullM6HdrMem c' ext' s' ⋆ R) m') (hQ : S5PreprocQ c F0 s R Q)
    (hk : ∀ c'' ext'' s'' m'', FullCfgCompat c c'' → FullM6HdrInv c'' F0 ext'' s'' →
      s''.core.cur_level = 0 → s''.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c'' ext'' s'' ⋆ R) m'' → wp Γ Q X k_ok m'') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var c'.hdr, ()) fun p =>
      Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst) (Expr.ret (Arg.imm 20, ()))
        (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 1, ())) fun p_2 =>
        Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.imm 0, ())) k_ok)) m' := by
  c0_call hCompact
  refine ⟨c', F0, ext', s', R, rfl, hinv', hm',
    fun rC c'' ext'' s'' m'' hcmpC hinv'' hrC _ hfuC huC h1C hm'' => ?_⟩
  have hcmp'' := hcmp.trans hcmpC
  have hfu'' := Nat.le_trans hfuC hfu'
  c0_hfast_nogrp
  · exact hQ 20#64 c'' ext'' s'' m'' hcmp'' hinv''.sparse.lengths hinv''.cfgOk hinv''.extOk
      (Or.inr (Or.inr (Or.inr rfl))) hfu'' (fun _ => huC ‹_›) (fun h => by cases h)
      (fun h => by cases h) hm''
  · exact hQ 0#64 c'' ext'' s'' m'' hcmp'' hinv''.sparse.lengths hinv''.cfgOk hinv''.extOk
      (Or.inl rfl) hfu'' (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm''
  · exact hk c'' ext'' s'' m'' hcmp'' hinv'' (h1C ‹_›) hfu'' hm''

/-! ## 2. Sweep-Propagate Loop & Post-Probe Stage -/

private theorem s5_preproc_sweep_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext0 : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {Js_out : Cont []}
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hQ : S5PreprocQ c F0 s R Q)
    (hinv0 : FullM6HdrInv c F0 ext0 s0) (hcl0 : s0.core.cur_level = 0)
    (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat) (hm0 : (FullM6HdrMem c ext0 s0 ⋆ R) m0)
    (hJs : ∀ ext' s' m', FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (FullM6HdrMem c ext' s' ⋆ R) m' →
      Js_out () m') :
    wp Γ Q X (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
        Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump Js_out ())) Blocks.nil)
          fun Js_brk => Expr.group (sig := [[]]) (fun Js_2 => Blocks.cons (fun _ =>
            Expr.jnz (Arg.imm true)
              (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_20 =>
                Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                    (Arg.var p_20.fst, Arg.imm 2, ())) fun p_21 =>
                Expr.jnz (Arg.var p_21.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                      (Arg.var p_20.fst, Arg.imm 3, ())) fun p_22 =>
                  Expr.jnz (Arg.var p_22.fst) (Expr.jump Js_brk.fst ())
                    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p_23 =>
                    Expr.load i64 (Arg.var p_23.fst) fun ld =>
                    Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                        (Arg.var ld, Arg.imm 0, ())) fun p_24 =>
                    Expr.jnz (Arg.var p_24.fst) (Expr.jump Js_brk.fst ())
                      (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                          (Arg.var c.hdr, ()) fun p_25 =>
                        Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                            (Arg.var p_25.fst, Arg.imm 1, ())) fun p_26 =>
                        Expr.jnz (Arg.var p_26.fst) (Expr.ret (Arg.imm 20, ()))
                          (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                              (Arg.var p_25.fst, Arg.imm 2, ())) fun p_27 =>
                          Expr.jnz (Arg.var p_27.fst) (Expr.jump Js_brk.fst ())
                            (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                                (Arg.var p_20.fst, Arg.imm 0, ())) fun p_28 =>
                            Expr.jnz (Arg.var p_28.fst)
                              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 152, ()))
                                  fun p_29 =>
                                Expr.load i64 (Arg.var p_29.fst) fun ld_p =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 144, ()))
                                    fun p_30 =>
                                  Expr.load i64 (Arg.var p_30.fst) fun ld_t =>
                                  Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
                                      (Arg.var ld_p, Arg.var ld_t, ())) fun p_31 =>
                                  Expr.jnz (Arg.var p_31.fst) (Expr.jump Js_brk.fst ())
                                    (Expr.jump Js_2.fst ()))
                              (Expr.jump Js_2.fst ())))))))
              (Expr.jump Js_brk.fst ())) Blocks.nil)
            fun Js => Expr.jump Js.fst ()) Blocks.nil)
      fun Js_1 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_18 =>
      Expr.load i64 (Arg.var p_18.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_19 =>
      Expr.jnz (Arg.var p_19.fst) (Expr.jump Js_1.fst ())
        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 144, ())) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
        Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ()) (Expr.jump Js_out ()))) m0 := by
  refine wp_join_group (ts := []) (fun _ mW => ∃ extW sW,
      FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
      sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
  · rintro _ _ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
    try dsimp only [Blocks.get_here]
    refine wp_join_group (ts := []) (fun _ mB => ∃ extB sB,
        FullM6HdrInv c F0 extB sB ∧ sB.core.cur_level = 0 ∧
        sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB sB ⋆ R) mB) ?_ ?_
    · rintro _ _ mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩
      refine wp_m6Hdr_focus_frame hmB fun hmBf => ?_
      c0_hfast_nogrp
      exact hJs extB _ _ (s5_preproc_with_unflushed0 hinvB) hclB hfuB
        (fullM6HdrMem_unfocus (by assumption))
    · intro Jbrk hJbrk
      refine wp_loop_group (ts := [])
        (fun rem () mL => ∃ extL sL, rem = c.max_vars - sL.core.trail_end ∧
          FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL) ?_ ?_
      · rintro L rem ⟨⟩ mL ih ⟨extL, sL, rfl, hinvL, hclL, hfuL, hmL⟩
        refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
        refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        obtain ⟨F_curL, hwL⟩ := hinvL.sparse.1.witness
        c0_call hSweep
        refine ⟨c, F0, F_curL, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl,
          hinvL.sparse.lengths, hwL, hinvL.sparse.2.2.1, hinvL.sparse.2.2.2.2,
          (fun hpos => absurd hpos (by omega)), hmLf,
          fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
            wlen' wu' fred' ni' nr' nb' oom' sc' mA
            hlenA hsr_dom hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 _ hmA => ?_⟩
        let sAc : FullCoreState :=
          { sL.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        let sA : FullState := { core := sAc, scratch := sc' }
        have hinvA : FullM6HdrInv c F0 extL sA :=
          FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk
            ⟨⟨hlenA, ⟨F_curL, hwA⟩⟩, hinvL.sparse.2.1, hndA,
              ⟨hllA, (by change sc'.extend_len ≤ c.extend_cap
                         rw [hextA]; exact hinvL.sparse.2.2.2.1.2)⟩,
              hinvL.sparse.2.2.2.2⟩
        have hmA' := fullM6HdrMem_unfocus hmA
        c0_hfast_nogrp
        · exact hQ 20#64 c extL sA mA (FullCfgCompat.refl c) hlenA hinvA.cfgOk hinvA.extOk
            (Or.inr (Or.inr (Or.inr rfl))) hfuL (fun _ => (hsr2 ‹_›).2)
            (fun h => by cases h) (fun h => by cases h) hmA'
        · exact hJbrk () mA ⟨extL, sA, hinvA, hclL, hfuL, hmA'⟩
        · exact hJbrk () mA ⟨extL, sA, hinvA, hclL, hfuL, hmA'⟩
        · refine s5_preproc_bcp rfl hProp hinvA hclL hfuL hmA'
            fun pr extB sB mB hinvB hclB hfuB hteB hpr hpeqB huB hmB => ?_
          refine wp_m6Hdr_focus_frame hmB fun hmBf => ?_
          c0_hfast_nogrp
          · exact hQ 20#64 c extB sB mB (FullCfgCompat.refl c) hinvB.sparse.lengths hinvB.cfgOk
              hinvB.extOk (Or.inr (Or.inr (Or.inr rfl))) hfuB (fun _ => huB ‹_›)
              (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf)
          · exact hJbrk () mB ⟨extB, sB, hinvB, hclB, hfuB, fullM6HdrMem_unfocus hmBf⟩
          · exact hJbrk () mB ⟨extB, sB, hinvB, hclB, hfuB, fullM6HdrMem_unfocus hmBf⟩
          · have hpr0 : pr = 0#64 := by
              rcases hpr with rfl | rfl | rfl <;> first | rfl | contradiction
            have hpeq := hpeqB hpr0
            have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
            have hte_le := hinvB.sparse.lengths.core_ok.trail_end_le
            have hcv_le := hinvB.sparse.lengths.core_ok.cur_vars_le
            exfalso
            have hlt : ¬ sB.core.trail_end % 2 ^ 64 ≤ sB.core.propagated % 2 ^ 64 := by assumption
            rw [hpeq] at hlt; exact hlt (Nat.le_refl _)
          · have hsr1_eq : sr = 1#64 := by
              rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
            have hte_inc := (hsr1 hsr1_eq).2
            change te' ≤ sB.core.trail_end at hteB
            have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
            have hte_le := hinvB.sparse.lengths.core_ok.trail_end_le
            have hcv_le := hinvB.sparse.lengths.core_ok.cur_vars_le
            exact ih (c.max_vars - sB.core.trail_end) () mB (by omega)
              ⟨extB, sB, rfl, hinvB, hclB, hfuB, fullM6HdrMem_unfocus hmBf⟩
      · intro L hL
        c0_hfast_nogrp
        exact hL (c.max_vars - sW.core.trail_end) () mW ⟨extW, sW, rfl, hinvW, hclW, hfuW, hmW⟩
  · intro J1 hJ1
    refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
    c0_hfast_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩
    · exact hJs ext0 s0 m0 hinv0 hcl0 hfu0 (fullM6HdrMem_unfocus hm0f)

private theorem s5_preproc_post_probe {Γ : Env} {c c' : FullCfg} {F0 : CNF Nat}
    {ext' : List (BitVec 64)} {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hcmp' : FullCfgCompat c c') (hinv' : FullM6HdrInv c' F0 ext' s')
    (hcl' : s'.core.cur_level = 0) (hfu' : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm' : (FullM6HdrMem c' ext' s' ⋆ R) m') (hQ : S5PreprocQ c F0 s R Q) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c'.hdr, Arg.imm 1024, ())) fun p_39 =>
        Expr.load i64 (Arg.var p_39.fst) fun ld_1 =>
        Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var ld_1, Arg.imm 0, ())) fun p_40 =>
        Expr.jnz (Arg.var p_40.fst) (Expr.ret (Arg.imm 20, ()))
          (Expr.let_ (Op.mk (.add i64) (Arg.var c'.hdr, Arg.imm 760, ())) fun p_41 =>
          Expr.load i64 (Arg.var p_41.fst) fun ld_2 =>
          Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var ld_2, Arg.imm 0, ())) fun p_42 =>
          Expr.jnz (Arg.var p_42.fst) (Expr.ret (Arg.imm 0, ()))
            (Expr.let_ (Op.mk (.add i64) (Arg.var c'.hdr, Arg.imm 792, ())) fun p_43 =>
            Expr.load i64 (Arg.var p_43.fst) fun ld_3 =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var ld_3, Arg.imm 0, ())) fun p_44 =>
            Expr.jnz (Arg.var p_44.fst) (Expr.ret (Arg.imm 10, ()))
              (Expr.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                  (Arg.var c'.hdr, Arg.imm 100, ()) fun p_45 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c'.hdr, Arg.imm 976, ())) fun p_46 =>
                Expr.store (t := i64) (Arg.var p_45.fst) (Arg.var p_46.fst)
                  (Expr.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                      (Arg.var c'.hdr, Arg.imm 500, ()) fun p_47 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c'.hdr, Arg.imm 992, ())) fun p_48 =>
                    Expr.store (t := i64) (Arg.var p_47.fst) (Arg.var p_48.fst)
                      (Expr.ret (Arg.imm 1, ()))))))) Blocks.nil)
      fun Js =>
      Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var c'.hdr, ())
        fun p_38 =>
      Expr.jnz (Arg.var p_38.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var c'.hdr, ()) fun p =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_39 =>
          Expr.jnz (Arg.var p_39.fst) (Expr.ret (Arg.imm 20, ()))
            (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 1, ()))
                fun p_40 =>
              Expr.jnz (Arg.var p_40.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump Js.fst ())))
        (Expr.jump Js.fst ())) m' := by
  refine wp_join_group (ts := []) (fun _ m6 => ∃ c6 ext6 s6,
      FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext6 s6 ∧ s6.core.cur_level = 0 ∧
      s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c6 ext6 s6 ⋆ R) m6) ?_ ?_
  · rintro _ _ m6 ⟨c6, ext6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
    try dsimp only [Blocks.get_here]
    rw [hcmp'.hdr, ← hcmp6.hdr]
    refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
    c0_hfast_nogrp
    · exact hQ 20#64 c6 ext6 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk hinv6.extOk
        (Or.inr (Or.inr (Or.inr rfl))) hfu6 (fun _ => fullM6HdrInv_inconsistent_unsat hinv6 ‹_›)
        (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm6f)
    · exact hQ 0#64 c6 ext6 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk hinv6.extOk
        (Or.inl rfl) hfu6 (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
        (fullM6HdrMem_unfocus hm6f)
    · exact hQ 10#64 c6 ext6 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk hinv6.extOk
        (Or.inr (Or.inr (Or.inl rfl))) hfu6 (fun h => by cases h) (fun h => by cases h)
        (fun _ => hinv6.sparse.2.2.2.1.2) (fullM6HdrMem_unfocus hm6f)
    · c0_call hScale
      refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext6 ⋆ R, rfl, hinv6.sparse.lengths,
        hm6f, fun sd1 => ?_⟩
      c0_hfast_nogrp; c0_call hScale
      refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext6 ⋆ R, rfl,
        (fullState_upd_probe_step hinv6.sparse.lengths sd1 s6.scratch.probings).1,
        by assumption, fun sd2 => ?_⟩
      c0_hfast_nogrp
      have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd1 s6.scratch.probings
      have hst6' := fullState_upd_elim_step hst6.1 sd2 s6.scratch.eliminations
        s6.scratch.elim_bound
      have hinv6' := fullM6HdrInv_of_probeStep hinv6 (probeStep_trans hst6 hst6')
      exact hQ 1#64 c6 ext6 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk hinv6'.extOk
        (Or.inr (Or.inl rfl)) (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
        (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
  · intro J2 hJ2
    refine wp_m6Hdr_focus_frame hm' fun hm'f => ?_
    c0_hfast_nogrp; c0_call hCompNeed
    refine ⟨c', s', m6ExtMem (m6ExtAddr c'.hdr) ext' ⋆ R, rfl, hinv'.sparse.lengths,
      by have := hinv'.sparse.lengths.core_ok.trail_end_le
         have := hinv'.sparse.lengths.core_ok.cur_vars_le
         have := c'.hmaxv; unfold dimacsBound at *; omega,
      hm'f, fun need _ => ?_⟩
    c0_hfast_nogrp
    · exact s5_preproc_call_compact hCompact hcmp' hinv' hfu' (fullM6HdrMem_unfocus hm'f) hQ
        fun c6 ext6 s6 m6 hcmp6 hinv6 hcl6 hfu6 hm6 => by
          c0_hfast_nogrp; exact hJ2 () m6 ⟨c6, ext6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
    · exact hJ2 () m' ⟨c', ext', s', hcmp', hinv', hcl', hfu', fullM6HdrMem_unfocus hm'f⟩

/-! ## 3. Top-Level `full_preprocess_m6_s5_wp` -/

theorem full_preprocess_m6_s5_wp (Γ : Env)
    (hLuckyLate : ∀ a m Q X, step13LuckyLateM6Spec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_preprocess_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_preprocess_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  · exact hQ 0#64 c ext s m (FullCfgCompat.refl c) hinv.sparse.lengths hinv.cfgOk hinv.extOk
      (Or.inl rfl) (Nat.le_refl _) (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fullM6HdrMem_unfocus hmf)
  · exact hQ 0#64 c ext s m (FullCfgCompat.refl c) hinv.sparse.lengths hinv.cfgOk hinv.extOk
      (Or.inl rfl) (Nat.le_refl _) (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fullM6HdrMem_unfocus hmf)
  · c0_call hLuckyLate
    refine ⟨c, F0, ext, s, R, rfl, hinv, fullM6HdrMem_unfocus hmf,
      fun lk ext1 s1 m1 hlen1 hext1 hlk hfu1 _ hu1 hsp1 h10_1 hm1 => ?_⟩
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    let s1' : FullState :=
      { s1 with scratch := { s1.scratch with search_ticks := s.scratch.search_ticks } }
    have hlen1' : s1'.LengthsOk c :=
      ⟨hlen1.core_ok, { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }⟩
    c0_hfast_nogrp
    · rw [‹lk = 20#64›]
      exact hQ 20#64 c ext1 s1' _ (FullCfgCompat.refl c) hlen1' hinv.cfgOk hext1
        (Or.inr (Or.inr (Or.inr rfl))) hfu1 (fun _ => hu1 ‹_›) (fun h => by cases h)
        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
    · rw [‹lk = 10#64›]
      exact hQ 10#64 c ext1 s1' _ (FullCfgCompat.refl c) hlen1' hinv.cfgOk hext1
        (Or.inr (Or.inr (Or.inl rfl))) hfu1 (fun h => by cases h) (fun h => by cases h)
        (fun _ => h10_1 ‹_›) (fullM6HdrMem_unfocus (by assumption))
    · have h02 : lk = 0#64 ∨ lk = 2#64 := by
        rcases hlk with rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr rfl | contradiction
      have ⟨hinv1, _⟩ := hsp1 h02
      have hinv1' := s5_preproc_with_searchTicks hinv1 s.scratch.search_ticks
      exact hQ 20#64 c ext1 s1' _ (FullCfgCompat.refl c) hlen1' hinv1'.cfgOk hext1
        (Or.inr (Or.inr (Or.inr rfl))) hfu1
        (fun _ => fullM6HdrInv_inconsistent_unsat hinv1' ‹_›) (fun h => by cases h)
        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
    · have h02 : lk = 0#64 ∨ lk = 2#64 := by
        rcases hlk with rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr rfl | contradiction
      have ⟨hinv1, hcl1⟩ := hsp1 h02
      have hinv1' := s5_preproc_with_searchTicks hinv1 s.scratch.search_ticks
      refine s5_preproc_bcp rfl hProp hinv1' hcl1 hfu1 (fullM6HdrMem_unfocus (by assumption))
        fun pr ext2 s2 m2 hinv2 hcl2 hfu2 _ _ _ hu2 hm2 => ?_
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hfast_nogrp
      · exact hQ 20#64 c ext2 s2 m2 (FullCfgCompat.refl c) hinv2.sparse.lengths hinv2.cfgOk
          hinv2.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu2 (fun _ => hu2 ‹_›)
          (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm2f)
      · exact hQ 0#64 c ext2 s2 m2 (FullCfgCompat.refl c) hinv2.sparse.lengths hinv2.cfgOk
          hinv2.extOk (Or.inl rfl) hfu2 (fun h => by cases h) (fun h => by cases h)
          (fun h => by cases h) (fullM6HdrMem_unfocus hm2f)
      · exact hQ 0#64 c ext2 s2 m2 (FullCfgCompat.refl c) hinv2.sparse.lengths hinv2.cfgOk
          hinv2.extOk (Or.inl rfl) hfu2 (fun h => by cases h) (fun h => by cases h)
          (fun h => by cases h) (fullM6HdrMem_unfocus hm2f)
      · refine wp_join_group (ts := []) (fun _ m3 => ∃ ext3 s3,
            FullM6HdrInv c F0 ext3 s3 ∧ s3.core.cur_level = 0 ∧
            s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext3 s3 ⋆ R) m3) ?_ ?_
        · rintro _ _ m3 ⟨ext3, s3, hinv3, hcl3, hfu3, hm3⟩
          try dsimp only [Blocks.get_here]
          refine wp_join_group (ts := []) (fun _ m4 => ∃ c4 ext4 s4,
              FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext4 s4 ∧ s4.core.cur_level = 0 ∧
              s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c4 ext4 s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, ext4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩
            try dsimp only [Blocks.get_here]
            rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hfast_nogrp
            · exact hQ 20#64 c4 ext4 s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inr rfl))) hfu4
                (fun _ => fullM6HdrInv_inconsistent_unsat hinv4 ‹_›) (fun h => by cases h)
                (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 0#64 c4 ext4 s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inl rfl) hfu4 (fun h => by cases h) (fun h => by cases h)
                (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 10#64 c4 ext4 s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inl rfl))) hfu4 (fun h => by cases h) (fun h => by cases h)
                (fun _ => hinv4.sparse.2.2.2.1.2) (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext4 ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hfast_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext4 ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hfast_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hfast_nogrp
              · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv4'.cfgOk hext5
                  (Or.inr (Or.inr (Or.inr rfl))) hfu5' (fun _ => hu5 ‹_›) (fun h => by cases h)
                  (fun h => by cases h) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hfast_nogrp
                · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inr (Or.inr (Or.inr rfl))) hfu5'
                    (fun _ => fullM6HdrInv_inconsistent_unsat hinv5 ‹_›) (fun h => by cases h)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h) (fun h => by cases h)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h) (fun h => by cases h)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact s5_preproc_post_probe hCompNeed hCompact hScale hcmp4 hinv5 hcl5 hfu5'
                    (fullM6HdrMem_unfocus hm5f) hQ
          · intro Jc1 hJc1
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_
            c0_hfast_nogrp
            · exact s5_preproc_call_compact hCompact (FullCfgCompat.refl c) hinv3 hfu3
                (fullM6HdrMem_unfocus hm3f) hQ
                fun c4 ext4 s4 m4 hcmp4 hinv4 hcl4 hfu4 hm4 => by
                  c0_hfast_nogrp; exact hJc1 () m4 ⟨c4, ext4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩
            · exact hJc1 () m3 ⟨c, ext3, s3, FullCfgCompat.refl c, hinv3, hcl3, hfu3,
                fullM6HdrMem_unfocus hm3f⟩
            · exact hJc1 () m3 ⟨c, ext3, s3, FullCfgCompat.refl c, hinv3, hcl3, hfu3,
                fullM6HdrMem_unfocus hm3f⟩
        · intro Js1 hJs1
          exact s5_preproc_sweep_loop hProp hSweep hQ hinv2 hcl2 hfu2 (fullM6HdrMem_unfocus hm2f)
            fun ext3 s3 m3 hinv3 hcl3 hfu3 hm3 => hJs1 () m3 ⟨ext3, s3, hinv3, hcl3, hfu3, hm3⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
