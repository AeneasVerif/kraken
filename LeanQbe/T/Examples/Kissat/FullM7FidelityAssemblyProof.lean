/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
public import LeanQbe.T.Examples.Kissat.FullM7CompactFixProof
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` `M7Fidelity` Closed Assembly Proof (`FullM7FidelityAssemblyProof`)

Complete closed `0`-hook UNSAT-only verification of `m7FidelityModule` (`413` fns, `0` `@[expose]`,
`0` `sorry` / `axiom`, `0` SAT model finding proofs):
1. Local `FullM4Compact.fullCompactNeededSpec`-backed `full_preprocess_fid2` and `full_simplify_m6`
   WP bridges matching `m7fix_1pct` (`FullM7CompactFix`).
2. `mfExtraRows` (`51` base helper rows + `6` excluded-from-base rows + `3` inserted Fidelity
   helper rows = `60` rows) + closed `M7FidelityEnv` / `m7FidelityEnv` over `m7FidBaseEnv`.
3. Closed `m7Fidelity_checkAcyclic`, `m7FidelityEnv_noExit`, `m7Fidelity_moduleOk`, UNSAT-only
   source & host soundness (`m7Fidelity_solve_bytes_sound`, `m7Fidelity_solve_bytes_host_sound`),
   and concrete Tier-3b UNSAT non-vacuity (`m7Fidelity_unsat_nv`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Fidelity

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. `FullM4Compact.fullCompactNeededSpec` Preprocess/Simplify Bridges -/

section PreprocessFid2Compact

private theorem fid2_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid2_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat := by
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

private abbrev Fid2PrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem fid2Pre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem fid2Pre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2Pre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  fid2Pre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem fid2Pre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : Fid2PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem fid2_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS
    let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine fid2_call_bcp rfl hProp hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact fid2Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (fid2_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, { hinvWP.sparseW.2.1 with
              arena := { hinvWP.sparseW.2.1.arena with len_ok := hinvWP.sparseW.2.1.arena.len_ok }
              watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
              }⟩⟩, hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem fid2_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : Fid2PrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact fid2Pre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact fid2Pre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

/-- Parametric `Func.wp` proof for `full_preprocess_fid2_body` against `fullM6PreprocessSpec`
(`fastel = 0`, `FullM4Compact.fullCompactNeededSpec`). -/
private theorem full_preprocess_fid2_compact_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ FullM7FidelitySchedFix.full_preprocess_fid2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullM7FidelitySchedFix.full_preprocess_fid2_body
    FullM7FidelitySchedFix.full_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine fid2_call_bcp rfl hProp hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact fid2Pre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (fid2_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact fid2Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact fid2Pre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3; have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact fid2Pre_ret20 hQ (.refl c) hlen3 hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (.refl c) hlen3 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · exact fid2Pre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_› hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · exact fid2Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
              FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
              s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hsteps_nogrp
            · exact fid2Pre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
            · exact fid2Pre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · exact fid2Pre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hsteps_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine FullM6Orch.m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hsteps_nogrp
              · exact fid2Pre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hsteps_nogrp
                · exact fid2Pre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · exact fid2Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                        FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                        s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                  · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                    rw [hcmp4.hdr, ← hcmp6.hdr]
                    refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                    c0_hsteps_nogrp
                    · exact fid2Pre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_› (fullM6HdrMem_unfocus hm6f)
                    · exact fid2Pre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                    · exact fid2Pre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                    · c0_call hScale
                      refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                      c0_hsteps_nogrp; c0_call hScale
                      refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        (fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings).1,
                        by assumption, fun sd4 => ?_⟩
                      c0_hsteps_nogrp
                      have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                        s6.scratch.probings
                      have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                        s6.scratch.elim_bound
                      have hinv6' := fullM6HdrInv_of_probeStep hinv6
                        (probeStep_trans hst6 hst6')
                      exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                        hinv6'.extOk (Or.inr (Or.inl rfl))
                        (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                        (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                  · exact fun _ hJC2 => wp_m6Hdr_focus_frame hm5 fun hm5f =>
                      fid2_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5 hcl5 hfu5' hm5f
                        hJC2 hQ
          · exact fun _ hJC1 =>
              fid2_pre_compact_step hCompNeed hCompact rfl (.refl c) hinv3 hcl3 hfu3' hm3 hJC1 hQ
    · exact fun _ hJ2 =>
        fid2_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

end PreprocessFid2Compact

private theorem mf_fullInv_of_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState}
    (hinv : FullM6HdrInv c F0 ext s) :
    s.core.cur_level < 2 ^ 64 ∧
    ((0#64 : BitVec 64).toNat < s.core.cur_level → (0#64 : BitVec 64).toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) := by
  obtain ⟨_, hw⟩ := hinv.sparse.1.witness
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hte := hinv.sparse.lengths.core_ok.trail_end_le
  have hcv := hinv.sparse.lengths.core_ok.cur_vars_le
  have hcl := hw.cur_level_le
  exact ⟨by omega, fun _ => by omega, hw.trail_lits_lt⟩

private theorem full_simplify_m6_compact_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Func.wp Γ full_simplify_m6_body a m Q X := by
  rintro ⟨h, dp, de, ⟨⟩⟩ m Q X hs
  rcases fullM6SimplifySpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_m6_body
  -- Step 1: backtrack to 0 if needed.
  refine wp_join_group (fun (_ : Tup Val []) m0 => ∃ s0, FullM6HdrInv c F0 ext s0 ∧
      s0.core.cur_level = 0 ∧ s0.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext s0 ⋆ R) m0) ?_ ?_
  · rintro _ _ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩
    -- Step 2: optional `do_probe -> full_probe_m6(h, false)`.
    refine wp_join_group (fun (_ : Tup Val []) m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · -- Step 3: optional `do_elim -> full_eliminate_m6(h, false)`.
        refine wp_join_group (fun (_ : Tup Val []) m2 => ∃ s2, FullM6HdrInv c F0 ext1 s2 ∧
            s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c ext1 s2 ⋆ R) m2) ?_ ?_
        · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
          refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) hfu2
              (fun _ => fullM6HdrInv_inconsistent_unsat hinv2 ‹_›) (fun h => by cases h) hm2
          · exact hQ 0#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inl rfl) hfu2
              (fun h => by cases h) (fun h => by cases h) hm2
          · -- Step 4: optional `compact_needed` -> `full_compact`.
            refine wp_join_group (fun (_ : Tup Val []) m3 => ∃ c3 s3,
                FullM4Compact.FullCfgCompat c c3 ∧
                FullM6HdrInv c3 F0 ext1 s3 ∧ s3.core.cur_level = 0 ∧
                s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c3 ext1 s3 ⋆ R) m3) ?_ ?_
            · rintro _ _ m3 ⟨c3, s3, hcmp3, hinv3, hcl3, hfu3, hm3⟩
              rw [← hcmp3.hdr]
              refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_
              c0_hsteps_nogrp
              · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inr rfl)) hfu3
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 ‹_›) (fun h => by cases h) hm3
              · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inl rfl) hfu3 (fun h => by cases h) (fun h => by cases h) hm3
              · exact hQ 1#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inl rfl)) hfu3 (fun h => by cases h)
                  (fun _ => ⟨hinv3, hcl3⟩) hm3
            · intro J3 hJ3
              c0_hsteps_nogrp; c0_call hCompNeed
              refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse.lengths,
                by have := hinv2.sparse.lengths.core_ok.trail_end_le
                   have := hinv2.sparse.lengths.core_ok.cur_vars_le
                   have := c.hmaxv; unfold dimacsBound at *; omega,
                hm2f, fun need _ => ?_⟩
              c0_hsteps_nogrp
              · c0_call hCompact
                refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse,
                  hm2f, fun rC c3 s3 m3 hcmp3 hsp3 hrC _ hfu3 hu3 h13 hm3 => ?_⟩
                have hcfg3 := M6HdrCfgOk_of_le (by rw [hcmp3.hdr]; exact M6HdrCfgOk_le hinv2.cfgOk)
                have hinv3 := FullM6HdrInv.mk_inv hcfg3 hinv2.extOk hsp3
                have hm3' := fullM6HdrMem_unfocus (hcmp3.hdr ▸ hm3)
                have hfu3' := Nat.le_trans hfu3 hfu2
                c0_hsteps_nogrp
                · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inr (Or.inr rfl)) hfu3' (fun _ => hu3 ‹_›)
                    (fun h => by cases h) hm3'
                · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inl rfl) hfu3' (fun h => by cases h) (fun h => by cases h) hm3'
                · exact hJ3 () m3 ⟨c3, s3, hcmp3, hinv3, h13 hc, hfu3', hm3'⟩
              · exact hJ3 () m2 ⟨c, s2, FullM4Compact.FullCfgCompat.refl c, hinv2, hcl2, hfu2, hm2⟩
        · intro J2 hJ2
          c0_hsteps_nogrp
          · c0_call hElim
            refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv1.sparse, hcl1,
              hm1f, fun rE s2 m2 hsp2 hcl2 hfu2 hr2 hu2 hm2 => ?_⟩
            have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
            have hm2' := fullM6HdrMem_unfocus hm2
            c0_hsteps_nogrp
            · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hsp2.lengths
                hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) (Nat.le_trans hfu2 hfu1)
                (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
            · exact hJ2 () m2 ⟨s2, hinv2, hcl2, Nat.le_trans hfu2 hfu1, hm2'⟩
          · exact hJ2 () m1 ⟨s1, hinv1, hcl1, hfu1, hm1⟩
    · intro J1 hJ1; c0_hsteps_nogrp
      · c0_call hProbe
        refine FullM6Orch.m6ProbeSpec_of hinv0 hcl0 hm0
          fun rP ext1 s1 m1 hlen1 hext1 hfu1 hr1 hu1 h11 hm1 => ?_
        have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [← hfu0]; exact hfu1
        c0_hsteps_nogrp
        · exact hQ 20#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 hinv0.cfgOk hext1
            (Or.inr (Or.inr rfl)) hfu1' (fun _ => hu1 ‹_›) (fun h => by cases h) hm1
        · obtain ⟨hinv1, hcl1⟩ := h11 (hr1.resolve_right ‹_›)
          exact hJ1 () m1 ⟨ext1, s1, hinv1, hcl1, hfu1', hm1⟩
      · exact hJ1 () m0 ⟨ext, s0, hinv0, hcl0, by rw [hfu0]; exact Nat.le_refl _, hm0⟩
  · intro J0 hJ0
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · obtain ⟨hcl_lt, htl_bd, htrl_bd⟩ := mf_fullInv_of_backtrack0 hinv
      obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
      c0_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths,
        hcl_lt, htl_bd, htrl_bd, hmf, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass'
          sc' m' hlen' hte' hprop' hcl' _ hsc _ _ hwi _ hm' => ?_⟩
      have hcl0' : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
      let s0c : FullCoreState :=
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      let s0 : FullState := { core := s0c, scratch := sc' }
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := hsc
      have hsp0 : FullSparseInv c F0 s0 :=
        ⟨⟨hlen', F_cur, hwi F0 F_cur hw (Nat.zero_le _)⟩,
          by unfold FullLitMarksClear FullMrkZero; exact hinv.sparse.2.1,
          by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
               fullArenaClauseLits; exact hinv.sparse.2.2.1,
          FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
          hinv.sparse.2.2.2.2⟩
      exact hJ0 () _ ⟨s0, FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp0,
        hcl0', rfl, fullM6HdrMem_unfocus hm'⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := hinv.sparse.1.witness.choose_spec.cur_level_le
        have := hinv.sparse.lengths.core_ok.trail_end_le
        have := hinv.sparse.lengths.core_ok.cur_vars_le
        have := c.hmaxv; unfold dimacsBound at *
        have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := ‹_›
        rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
      exact hJ0 () m ⟨s, hinv, hcl0, rfl, hm⟩



/-! ## 2. Closed `M7FidelityEnv` & Extra Helper Table (`60` Rows) -/

def mfHasBinFn : Fn :=
  ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.full_has_bin_body⟩

def mfMinMarkFn : Fn :=
  ⟨"full_min_mark", [i64, i32, i8], [], Full.full_min_mark_body⟩

def mfExtraBaseFns : List Fn :=
  [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
  , FullM7BcpHot.m7PropLitOvfFn
  , FullM7BcpHot.m7PropChronoFn
  , mfHasBinFn
  , mfMinMarkFn ] ++
  (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2 ++
  (FullM7AnalyzeSort.m7AnalyzeSort_fns.take 1 ++
    [ FullM7AnalyzeSort.m7SortTmpHeapFn
    , FullM7AnalyzeSort.m7SortTmpFn
    , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
        FullM6MinShrink.full_min_lit_dfs_m6_body⟩
    , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool],
        FullM6MinShrink.full_shrink_lower_m6_body⟩
    , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
        FullM6MinShrink.full_shrink_blk_bool_m6_body⟩ ]) ++
  FullM7Walk.m7WalkFns.take 10 ++
  [ ⟨"full_warmup_m7", [i64], [], FullM7Walk.full_warmup_m7_body⟩ ] ++
  FullM6VivBackbone.m6VivBackbone_fns.take 1 ++
  (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25

def mfExtraBaseRows : List SpecEntry :=
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool],
      FullM7BcpHot.fullPropLitOvfHotSpec, true⟩
  , ⟨"full_prop_chrono_hot", [i64, i64], [.bool],
      FullM7BcpHot.fullPropChronoHotSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩
  , ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩
  , ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], FullM6MinShrink.m6AnaSiftSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.m6SortAnaQsSpec, true⟩
  , ⟨"full_sort_tmp_sift_m7", [i64, i64, i64, i64, i64], [],
      Full.FullMinSpecs.fullSortTmpSiftSpec, true⟩
  , ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [],
      FullM7AnalyzeSort.m7SortTmpHeapSpec, true⟩
  , ⟨"full_sort_tmp", [i64], [], FullM7AnalyzeSort.m7SortTmpSpec, true⟩
  , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.m6MinLitDfsSpec, true⟩
  , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], FullM7Walk.m7CbInvSpec, true⟩
  , ⟨"full_walk_init_table_m7", [i64, i64], [], FullM7Walk.m7InitTableSpec, true⟩
  , ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.m7EffortSpec, true⟩
  , ⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.m7InitValsSpec, true⟩
  , ⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.m7CollectSpec, true⟩
  , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], FullM7Walk.m7BuildOccSpec, true⟩
  , ⟨"full_walk_break_m7", [i64, i32, i64], [i32], FullM7Walk.m7BreakSpec, true⟩
  , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], FullM7Walk.m7PickSpec, true⟩
  , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], FullM7Walk.m7FlipSpec, true⟩
  , ⟨"full_walk_save_min_m7", [i64, i64, .bool], [], FullM7Walk.m7SaveMinSpec, true⟩
  , ⟨"full_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩ ] ++
  FullM6VivBackbone.m6VivBackboneSpecTable.take 1 ++
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25

def mfExtraRows : List SpecEntry :=
  mfExtraBaseRows ++
  [ ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
  , ⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩
  , ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_walk_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool],
      FullM7FidelityCore.fidBvaMatchLargeSpec, true⟩
  , ⟨"full_reorder_sift_fid", [i64, i64, i64], [],
      FullM7FidelityCore.fidReorderSiftSpec, true⟩
  , ⟨"m6_hdr_decide_fid", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ ]

private theorem mfExtraRows_nodup : (mfExtraRows.map SpecEntry.name).Nodup := by
  show ([ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
    , "full_has_bin", "full_min_mark", "full_ana_sift_m6", "full_sort_ana_qs_m6"
    , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp"
    , "full_min_lit_dfs_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6"
    , "full_walk_cb_inv_m7", "full_walk_init_table_m7", "full_walk_effort_m7"
    , "full_walk_init_vals_m7", "full_walk_collect_m7", "full_walk_build_occ_m7"
    , "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7", "full_walk_save_min_m7"
    , "full_warmup_m7", "full_add_bin_m6"
    , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
    , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
    , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
    , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
    , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
    , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
    , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
    , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
    , "full_viv_clear_tier_m6"
    , "full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7"
    , "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"
    , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ] :
      List String).Nodup
  decide

private theorem mfExtraRows_noExit : ∀ e ∈ mfExtraRows, e.noExit = true := by
  intro e he
  exact List.all_eq_true.mp (by t_kernel_rfl : mfExtraRows.all (·.noExit) = true) e he

private theorem mf_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (mf_ofTable_name_mem h)

/-- Names routed exclusively through `mfExtraRows` rather than `m7FidBaseEnv`. -/
def mfExclNames : List Sym :=
  [ "full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7"
  , "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"
  , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ]

/-- Closed `M7Fidelity` environment extending `m7FidBaseEnv` with `mfExtraRows` (`51` base
helpers, `6` excluded-from-base specs, and `3` inserted Fidelity helpers). -/
inductive M7FidelityEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ∉ mfExclNames →
      Γ f as bs xs m Q X → M7FidelityEnv Γ f as bs xs m Q X
  | extra {f as bs xs m Q X} :
      Env.ofTable mfExtraRows f as bs xs m Q X →
      M7FidelityEnv Γ f as bs xs m Q X

/-- Canonical closed `Env` for `m7FidelityModule` (`413` fns, `0` hooks, zero SAT proofs). -/
def m7FidelityEnv : Env := M7FidelityEnv m7FidBaseEnv

theorem m7FidelityEnv_noExit : ∀ f as bs xs m Q X X',
    m7FidelityEnv f as bs xs m Q X → m7FidelityEnv f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base hne hb =>
    exact .base hne (m7FidBaseEnv_noExit _ _ _ _ _ _ _ _ hb)
  | extra he => exact .extra (Env.ofTable_noExit mfExtraRows_noExit _ _ _ _ _ _ _ _ he)

theorem m7FidelityEnv_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    m7FidelityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  constructor
  · intro h
    cases h with
    | base _ hb => exact m7FidBase_solve_bytes_iff.mp hb
    | extra he => exact False.elim (absurd (mf_ofTable_name_mem he) (by decide))
  · intro hs
    exact M7FidelityEnv.base (by decide) (m7FidBase_solve_bytes_iff.mpr hs)

theorem m7FidelityEnv_solve_bytes {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7FidSolveBytesSpec xs m Q X) :
    m7FidelityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  m7FidelityEnv_solve_bytes_iff.mpr (m7FidSolveBytesSpec_monoX hs)

private theorem mf_extra_at {Γ : Env} (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → M7FidelityEnv Γ nm as bs xs m Q X := fun xs m Q X hs =>
  M7FidelityEnv.extra (Env.ofTable_of_mem (List.mem_of_getElem? hi) mfExtraRows_nodup
    (hno xs m Q X hs))

private theorem mf_extra_elim {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ mfExtraRows)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable mfExtraRows nm as bs xs m Q X) :
    sp xs m Q (fun _ _ _ _ => False) :=
  env_ofTable_elim_of_mem hmem mfExtraRows_nodup h

private theorem mf_extra_elim_cast {e : SpecEntry} {fn : Fn}
    (hmem : e ∈ mfExtraRows)
    (hnm : e.name = fn.name) (has : e.as = fn.as) (hrs : e.rs = fn.rs)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Env.ofTable mfExtraRows fn.name fn.as fn.rs xs m Q X) :
    e.cast has hrs xs m Q X := by
  cases e with
  | mk enm eas ers esp enx =>
    dsimp only at hnm has hrs
    cases hnm; cases has; cases hrs
    exact env_ofTable_elim_of_mem hmem mfExtraRows_nodup h

private theorem mf_tableImpl_getElem {Γ : Env} :
    ∀ {fs : List Fn} {rs : List SpecEntry} (i : Nat)
      (h1 : i < fs.length) (h2 : i < rs.length),
      TableImpl Γ fs rs → SpecEntry.Impl Γ (fs[i]'h1) (rs[i]'h2)
  | [], _, i, h1, _, _ => absurd h1 (Nat.not_lt_zero i)
  | _ :: _, [], _, _, _, ht => False.elim ht
  | _ :: _, _ :: _, 0, _, _, ht => ht.1
  | _ :: _, _ :: _, i + 1, h1, h2, ht =>
    mf_tableImpl_getElem i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) ht.2

private def mfBadNames : List Sym :=
  [ "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr", "full_compact_needed"
  , "full_walk_m7", "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr"
  , "full_analyze_core_m6", "full_analyze_m6_hdr"
  , "full_walk_warmup_m7", "full_walk", "full_rephase"
  , "full_probe_tail_m6", "full_probe_m6", "full_preprocess_m6", "full_simplify_m6"
  , "full_search_m6", "kissat_solve_bytes_m6", "full_preprocess", "full_search"
  , "kissat_solve_bytes"
  , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ]

private def mfOkName (f : Sym) : Bool :=
  !(mfBadNames.any (· == f))

mutual
private def mfNoCallBad {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => mfNoCallBad (k (Tup.units _))
  | .load _ _ k => mfNoCallBad (k ())
  | .store _ _ k => mfNoCallBad k
  | .call f _ k => mfOkName f && mfNoCallBad (k (Tup.units _))
  | .jnz _ t e => mfNoCallBad t && mfNoCallBad e
  | .jump _ _ | .ret _ | .hlt | .exit _ _ => true
  | .group (sig := sig) bodies k =>
      mfBlocksNoCallBad (bodies (Tup.units sig)) && mfNoCallBad (k (Tup.units sig))

private def mfBlocksNoCallBad {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => mfNoCallBad (b (Tup.units _)) && mfBlocksNoCallBad bs
end

mutual
private theorem mf_callsOk_filter {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.callsOk allowed exits → mfNoCallBad e = true →
    e.callsOk (allowed.filter (fun s => mfOkName s.1)) exits
  | .let_ _ k, hc, hn => mf_callsOk_filter (k (Tup.units _)) hc hn
  | .load _ _ k, hc, hn => mf_callsOk_filter (k ()) hc hn
  | .store _ _ k, hc, hn => mf_callsOk_filter k hc hn
  | .call f (as := _) (bs := bs) _ k, hc, hn => by
    change (mfOkName f && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨List.mem_filter.mpr ⟨hc.1, h1⟩, mf_callsOk_filter (k (Tup.units bs)) hc.2 h2⟩
  | .jnz _ t e, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mf_callsOk_filter t hc.1 h1, mf_callsOk_filter e hc.2 h2⟩
  | .jump _ _, hc, _ | .ret _, hc, _ | .hlt, hc, _ | .exit _ _, hc, _ => hc
  | .group (sig := sig) bodies k, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mf_blocksCallsOk_filter (bodies (Tup.units sig)) hc.1 h1,
      mf_callsOk_filter (k (Tup.units sig)) hc.2 h2⟩

private theorem mf_blocksCallsOk_filter {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.callsOk allowed exits → mfBlocksNoCallBad bs = true →
    bs.callsOk (allowed.filter (fun s => mfOkName s.1)) exits
  | _, .nil, _, _ => trivial
  | _, .cons b bs, hc, hn => by
    change (_ && _) = true at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    exact ⟨mf_callsOk_filter (b (Tup.units _)) hc.1 h1, mf_blocksCallsOk_filter bs hc.2 h2⟩
end

private theorem mf_all_nonbad_no_bad :
    (m7Fns.filter (fun fn => mfOkName fn.name)).all
      (fun fn => mfNoCallBad (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))) =
      true := by
  t_kernel_rfl

private theorem mf_extraBaseFns_sigs :
    mfExtraBaseRows.map (fun e => (e.name, e.as, e.rs)) = mfExtraBaseFns.map Fn.sig := by
  t_kernel_rfl

private theorem mf_fn_81 : m7Fns[81]? = some FullM7BcpHot.m7PropLitOvfFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem mf_fn_82 : m7Fns[82]? = some FullM7BcpHot.m7PropChronoFn := by
  rw [m7_get_p1 (by decide)]; t_kernel_rfl

private theorem mf_extraBaseFns_sub : ∀ f ∈ mfExtraBaseFns, f ∈ m7Fns := by
  have hf54 : m7Fns[54]? = some ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf56 : m7Fns[56]? = some ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩ := by
    rw [m7_get_p1 (by decide)]; t_kernel_rfl
  have hf124 : m7Fns[124]? = some mfMinMarkFn := by
    rw [show (124 : Nat) = 112 + 12 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf130 : m7Fns[130]? = some ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.full_min_lit_dfs_m6_body⟩ := by
    rw [show (130 : Nat) = 112 + 18 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf132 : m7Fns[132]? = some ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool],
      FullM6MinShrink.full_shrink_lower_m6_body⟩ := by
    rw [show (132 : Nat) = 112 + 20 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf133 : m7Fns[133]? = some ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.full_shrink_blk_bool_m6_body⟩ := by
    rw [show (133 : Nat) = 112 + 21 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf165 : m7Fns[165]? = some ⟨"full_warmup_m7", [i64], [],
      FullM7Walk.full_warmup_m7_body⟩ := by
    rw [show (165 : Nat) = 112 + 53 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hf175 : m7Fns[175]? = some mfHasBinFn := by
    rw [show (175 : Nat) = 112 + 63 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
  have hfAna2 : (m7FnsPart2.drop 4).take 2 = (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2 := by
    t_kernel_rfl
  have hfSt3 : (m7FnsPart2.drop 15).take 3 =
      FullM7AnalyzeSort.m7AnalyzeSort_fns.take 1 ++
        [FullM7AnalyzeSort.m7SortTmpHeapFn, FullM7AnalyzeSort.m7SortTmpFn] := by
    t_kernel_rfl
  have hfWlk10 : (m7FnsPart2.drop 42).take 10 = FullM7Walk.m7WalkFns.take 10 := by
    t_kernel_rfl
  have hf177 : (m7FnsPart2.drop 65).take 1 = FullM6VivBackbone.m6VivBackbone_fns.take 1 := by
    t_kernel_rfl
  have hfViv : (m7FnsPart2.drop 79).take 25 =
      (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 := by t_kernel_rfl
  have mem_p2 : ∀ {f : Fn}, f ∈ m7FnsPart2 → f ∈ m7Fns := fun h =>
    List.mem_append_left _ (List.mem_append_right _ h)
  intro f hf
  simp only [mfExtraBaseFns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with ((((((rfl | rfl | rfl | rfl | rfl | rfl) | hana) |
    (hst | (rfl | rfl | rfl | rfl | rfl))) | hwlk) | rfl) | hab) | hviv
  · exact List.mem_of_getElem? hf54
  · exact List.mem_of_getElem? hf56
  · exact List.mem_of_getElem? mf_fn_81
  · exact List.mem_of_getElem? mf_fn_82
  · exact List.mem_of_getElem? hf175
  · exact List.mem_of_getElem? hf124
  · rw [← hfAna2] at hana
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hana))
  · have hmem3 : f ∈ (m7FnsPart2.drop 15).take 3 := by
      rw [hfSt3]; exact List.mem_append_left _ hst
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hmem3))
  · have hmem3 : FullM7AnalyzeSort.m7SortTmpHeapFn ∈ (m7FnsPart2.drop 15).take 3 := by
      rw [hfSt3]; exact List.mem_append_right _ List.mem_cons_self
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hmem3))
  · have hmem3 : FullM7AnalyzeSort.m7SortTmpFn ∈ (m7FnsPart2.drop 15).take 3 := by
      rw [hfSt3]; exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hmem3))
  · exact List.mem_of_getElem? hf130
  · exact List.mem_of_getElem? hf132
  · exact List.mem_of_getElem? hf133
  · rw [← hfWlk10] at hwlk
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hwlk))
  · exact List.mem_of_getElem? hf165
  · rw [← hf177] at hab
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hab))
  · rw [← hfViv] at hviv
    exact mem_p2 (List.mem_of_mem_drop (List.mem_of_mem_take hviv))

private theorem mf_fullLeaf_wp {fn : Fn} {sp : Spec fn.as fn.rs} (Γ : Env) (idx : Nat)
    (hfn : Full.fullFns[idx]? = some fn)
    (hrow : (Full.fullSpecTable Full.fullSolveBytesSpec)[idx]? =
      some ⟨fn.name, fn.as, fn.rs, sp, true⟩)
    (hcalls : fn.checkCallsOk [] [] = true)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → Func.wp Γ fn.body a m Q X := by
  have hndF : ((Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name).Nodup := by
    have hm := congrArg (List.map Prod.fst) (Full.fullSpecTable_sigs Full.fullSolveBytesSpec)
    have hn : (Full.fullSpecTable Full.fullSolveBytesSpec).map SpecEntry.name =
        Full.fullFns.map Fn.name := by
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    exact tbl_nodup_of_sigs (M := Full.fullModule) Full.full_acyclic hn
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem (List.mem_of_getElem? hfn)
  have ⟨hwf, _, hwp⟩ := Full.fullEnv_moduleOk.fnsOk pre fn post hsp
  have hco : fn.callsOk [] [] := Fn.callsOk_of_checkCallsOk hcalls
  intro xs m Q X hspec
  have henv : Full.fullEnv fn.name fn.as fn.rs xs m Q X :=
    Env.ofTable_of_mem (List.mem_of_getElem? hrow) hndF (hno xs m Q X hspec)
  exact wp_env_agree_of_callsOk
    (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    hco (fun _ _ _ h => nomatch h) m (hwp xs m Q X henv)

private theorem mf_hasBin_wp (Γ : Env) :
    ∀ a m Q X, Full.fullHasBinSpec a m Q X → Func.wp Γ Full.full_has_bin_body a m Q X :=
  mf_fullLeaf_wp (fn := mfHasBinFn) (sp := Full.fullHasBinSpec) Γ 97
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

private theorem mf_minMark_wp (Γ : Env) :
    ∀ a m Q X, Full.fullMinMarkSpec a m Q X → Func.wp Γ Full.full_min_mark_body a m Q X :=
  mf_fullLeaf_wp (fn := mfMinMarkFn) (sp := Full.fullMinMarkSpec) Γ 69
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

private theorem mf_base_at {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hne : nm ∉ mfExclNames := by decide)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → m7FidelityEnv nm as bs xs m Q X := fun xs m Q X hsp =>
  M7FidelityEnv.base hne (m7FidBase_row_mem hmem hno xs m Q X hsp)

private theorem mf_not_excl_of_ok {f : Sym} (hok : mfOkName f = true) : f ∉ mfExclNames := by
  intro hm
  simp only [mfExclNames, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mfOkName, mfBadNames] at hok

/-! ## 3. Closed `413/413` `m7Fidelity_moduleOk`, UNSAT Soundness & Tier-3b UNSAT Non-Vacuity -/

private theorem mf_ne_of_find_none {r0 g : Fn} (hrm : r0 ∈ m7FidRepls)
    (hfind : m7FidRepls.find? (fun r => r.name == g.name) = none) :
    g.name ≠ r0.name := by
  intro heq
  have h1 : (m7FidRepls.find? (fun r => r.name == g.name)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨r0, hrm, by simp [heq]⟩
  rw [hfind] at h1
  cases h1

private theorem mf_idx_119 : m7Fns[119]? = some m6aRestoreBumpAnaM6HdrFn := by
  rw [show (119 : Nat) = 112 + 7 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_120 : m7Fns[120]? = some m6aAnaFailedLitM6HdrFn := by
  rw [show (120 : Nat) = 112 + 8 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_150 : m7Fns[150]? = some m6oAnalyzeCoreM6Fn := by
  rw [show (150 : Nat) = 112 + 38 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_151 : m7Fns[151]? = some m6aAnalyzeM6HdrFn := by
  rw [show (151 : Nat) = 112 + 39 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_166 :
    m7Fns[166]? = some ⟨"full_walk_warmup_m7", [i64], [],
      FullM7Walk.full_walk_warmup_m7_body⟩ := by
  rw [show (166 : Nat) = 112 + 54 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_168 :
    m7Fns[168]? = some ⟨"full_walk", [i64], [], FullM7Walk.full_walk_warmup_m7_body⟩ := by
  rw [show (168 : Nat) = 112 + 56 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_169 : m7Fns[169]? = some FullM7AnalyzeSort.m7RephaseFn := by
  rw [show (169 : Nat) = 112 + 57 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl

private theorem mf_idx_404 : m7Fns[404]? = some m6oSimplifyM6Fn := by
  rw [show (404 : Nat) = 276 + 128 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mf_idx_406 : m7Fns[406]? = some FullM6Orch.m6oSolveBytesM6Fn := by
  rw [show (406 : Nat) = 276 + 130 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mf_idx_407 :
    m7Fns[407]? = some ⟨"full_preprocess", [i64], [i64], FullM6Orch.full_preprocess_body⟩ := by
  rw [show (407 : Nat) = 276 + 131 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mf_idx_408 :
    m7Fns[408]? = some ⟨"full_search", [i64], [i64], FullM6Orch.full_search_body⟩ := by
  rw [show (408 : Nat) = 276 + 132 by rfl, m7_get_p3]; t_kernel_rfl

private theorem mf_idx_409 : m7Fns[409]? = some FullM6Orch.m6oSolveBytesFn := by
  rw [show (409 : Nat) = 276 + 133 by rfl, m7_get_p3]; t_kernel_rfl

private def mfMidEnv : Env :=
  fun f as bs xs m Q X => mfOkName f = true ∧ m7FidBaseEnv f as bs xs m Q X

theorem m7Fidelity_checkAcyclic : m7FidelityModule.checkAcyclic = true := m7Fidelity_acyclic

private theorem mfPatchModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := mfPatchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hbWf : ∀ p ∈ befores, ∀ b ∈ p.2, b.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X)
    (hbWp : ∀ p ∈ befores, ∀ b ∈ p.2, ∀ xs m Q X,
      Γ' b.name b.as b.rs xs m Q X → Func.wp Γ' b.body xs m Q X) :
    ModuleOk Γ' { M with fns := mfPatchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk (mfPatchFns_wf hwfOrig hrWf hbWf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hfn⟩
  rcases List.mem_append.mp hfn with hins | hcur
  · rcases mem_mfPatchInsAt hins with ⟨hs, hm, hfn_hs⟩
    exact hbWp (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp hcur with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | some r =>
      intro xs m Q X hspec
      exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
    | none =>
      intro xs m Q X hspec
      rcases hFnWp g hg h with hNew | hPull
      · exact hNew xs m Q X hspec
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
        have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
        exact wp_env_agree_of_callsOk
          (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
          hcallsG (fun f as bs _ => hCallee f as bs) m
          (hwpG xs m Q X (hPull xs m Q X hspec))

/-- Closed `413/413` `ModuleOk` certifying `m7FidelityModule` (Target A, upstream Kissat 4.0.4)
under `m7FidelityEnv` with `0` external hooks, `0` `sorry`/`axiom`, and zero SAT model proofs. -/
theorem m7Fidelity_moduleOk : ModuleOk m7FidelityEnv m7FidelityModule := by
  have hbaseOk := m7FidBase_moduleOk
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc1Tail := m7FidPart1TailCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc2gu := m7Part2BvaGuRows_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have rWp := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.watchPush
  have rWd := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag
  have rRescaleMem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.rescale
  have rMrkRsnMem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.markReasons
  have rReduceM6Mem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reduceM6
  have rAnaCoreMem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.analyzeCoreM6
  have rReorderM6Mem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6
  have rPreM6Mem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.preprocessM6
  have rSimpM6Mem := m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6
  have rProbeTailMem := m7FidBase_probeTailM6_mem
  have rProbeMem := m7FidBase_probeM6_mem
  have rArSwp := mf_base_at (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.arenaSweep)
  have rSwpDense := mf_base_at m7FidBase_sweepDenseM6_mem
  have rRescale := mf_base_at rRescaleMem
  have rMrkRsn := mf_base_at rMrkRsnMem
  have rReduceM6 := mf_base_at rReduceM6Mem (hno := fun _ _ _ _ h => m6ReduceSpec_monoX h)
  have rAnaCore := mf_base_at rAnaCoreMem (hno := fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have rReorderM6 := mf_base_at rReorderM6Mem
  have rSimpM6 := mf_base_at rSimpM6Mem (hno := fun _ _ _ _ h => fullM6SimplifySpec_monoX h)
  have rDed1uip := mf_base_at m7FidBase_deduce1uipM6Hdr_mem
    (hno := fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h)
  have rIsqrt := mf_base_at hc1.isqrt
  have rIlog := mf_base_at hc1.ilog10
  have rRng := mf_base_at hc1.rngNext
  have rNext := mf_base_at hc1.arenaNext
  have rAllocCl := mf_base_at hc1.allocCl
  have rHeapUp := mf_base_at m7FidBase_heapUp_mem
  have rHeapDown := mf_base_at hc1.heapDown
  have rBumpVar := mf_base_at hc1.bumpVar
  have rBumpDecay := mf_base_at hc1.bumpDecay
  have rQueueMtf := mf_base_at hc1.queueMtf
  have rTickRel := mf_base_at hc1.tickRel
  have rEmaUpd := mf_base_at hc1.emaUpdate
  have rLog10 := mf_base_at hc1.log10Q16M7
    (hno := fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h)
  have rScaleM5 := mf_base_at hc1.scaleDeltaM5
  have rScaleD := mf_base_at hc1.scaleDelta
  have rALvl := mf_base_at hc1.assignLvl
  have rAsg := mf_base_at hc1.assign
  have rBt := mf_base_at hc1.backtrack
  have rUnw := mf_base_at hc1.unwatchLarge
  have rPI := mf_base_at hc1.propagateIgn
  have rProp := mf_base_at hc1.propagate
  have rPropS15 := m7_fullPropagate_to_bcpS15 rProp
  have rSync := mf_base_at hc1.hdrSyncLegacy (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rUpdTier := mf_base_at hc1.hdrUpdateTier (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rGetWm := mf_base_at hc1.hdrGetWm (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rSetWm := mf_base_at hc1.hdrSetWm (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDrInit := mf_base_at hc1.hdrDrInit (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)
  have rDrUpd := mf_base_at hc1.hdrDrUpdate (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)
  have rDrAllow := mf_base_at hc1.hdrDrAllow (hno := fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h)
  have rRecomp := mf_base_at hc1p.recomputeTiers (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rDelay := mf_base_at hc1p.delaying (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rRedD := mf_base_at hc1p.reduceDelay (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rBumpD := mf_base_at hc1p.bumpDelay (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rSortReds := mf_base_at hc1p.sortReds
  have rWpEnv := mf_base_at rWp
  have rWdEnv := mf_base_at rWd
  have rFixedBytes := mf_base_at m7FidBase_fixedBytes_mem
  have rAu := mf_base_at hc2.addUnit
  have rAddBin := mf_base_at hc2.addBin
  have rAddBinCan := m6_add_bin_m6_to_canon rAddBin
  have rDelBin := mf_base_at hc2.deleteBinary
  have rNDV := mf_base_at hc2.nextDecVar
  have rAnalyzeM6 := mf_base_at hc2.analyzeM6 (hno := fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h)
  have rRstDue := mf_base_at hc2.restartDue
  have rRst := mf_base_at hc2.restart
  have rRephase := mf_base_at hc2.rephase (hno := fun _ _ _ _ h => m7RephaseSpec_monoX h)
  have rEnterDense := mf_base_at hc2.enterDense
  have rRebuild := mf_base_at hc2.rebuildWatches
  have rAnaLit := mf_base_at hc2p.analyzeLit
  have rClearAna := mf_base_at hc2p.clearAna
  have rRstBump := mf_base_at hc2p.restoreBumpAna
    (hno := fun _ _ _ _ h => m6aRestoreBumpAnaSpec_monoX h)
  have rAnaFailed := mf_base_at hc2p.anaFailedLit
    (hno := fun _ _ _ _ h => m6aAnaFailedLitSpec_monoX h)
  have rMinShr := mf_base_at hc2p.minShrinkM6
    (hno := fun _ _ _ _ h => FullM7SpecBridges.m7MinShrinkSpec_monoX h)
  have rOneLit := mf_base_at hc2p.oneLitConfl
  have rLrnCl := mf_base_at hc2p.learnClause
  have rLucky := mf_base_at hc2p.lucky
  have rVivM6 := mf_base_at hc2p.vivifyM6Hdr (hno := fun _ _ _ _ h => m6aVivifySpec_monoX h)
  have rBackbone := mf_base_at hc2p.backboneM6
  have rTrans := mf_base_at hc2p.transitiveM6
  have rSubst := mf_base_at hc2p.substitute
  have rCongDense := mf_base_at hc2p.congruenceDense
  have rInitFresh := mf_base_at m7FidP3InitFreshVar_mem
  have rDedup := mf_base_at m7FidP3DedupBins_mem
  have rFlushUnits := mf_base_at m7FidBase_denseFlushUnits_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit _ _ _ _ h)
  have rFlushLg := mf_base_at m7FidBase_fwdFlushLarge_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdFlushLargeM6Spec_noExit _ _ _ _ h)
  have rReconn := mf_base_at m7FidBase_fwdReconnIrred_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdReconnectIrredM6Spec_noExit _ _ _ _ h)
  have rCheckCl := mf_base_at m7FidBase_fwdCheckCl_mem
    (hno := FullM7BveGates.fullFwdCheckClM7Spec_noExit)
  have rConnSub := mf_base_at m7FidBase_fwdConnSub_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdConnectSubsumerM6Spec_noExit _ _ _ _ h)
  have rColSort := mf_base_at m7FidBase_fwdColSort_mem
    (hno := fun _ _ _ _ h => FullM6BveFwd.fullFwdCollectSortM6Spec_noExit _ _ _ _ h)
  have rBveVar := mf_base_at m7FidBase_bveVar_mem
  have rBvePush := mf_base_at m7FidBase_bveHeapPush_mem
    (hno := FullM6BveFwd.fullBveHeapPushM6Spec_noExit)
  have rBvePop := mf_base_at m7FidBase_bveHeapPop_mem
    (hno := FullM6BveFwd.fullBveHeapPopM6Spec_noExit)
  have rBveNbrs := mf_base_at m7FidBase_bveCollectNbrs_mem
  have rElimDticks := mf_base_at m7FidP3ElimDticks_mem
  have rMinU64 := mf_base_at m7FidP3MinU64_mem
  have rFwdSub := mf_base_at (m7FidBase_bve_mem _ m7FidBveRows_specs.fwdSub)
  have rElimBve := mf_base_at m7FidBase_elimBveM7_mem
  have rFactor := mf_base_at m7FidP3Factor_mem
  have rElimM6 := mf_base_at (m7FidBase_bve_mem _ m7FidBveRows_specs.eliminateM6)
  have rCompact := mf_base_at hc3p.compact
  have rReorderQ := mf_base_at hc3p.reorderQueueM7
  have rDticks := mf_base_at hc3p.probeDticks (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rLuckyLate := mf_base_at hc3.luckyLateM7
    (hno := fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h)
  have rSwitchMode := mf_base_at hc3.switchModeM7
    (hno := fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h)
  have rDecideM7 := mf_base_at hc3.decideM7
    (hno := fun _ _ _ _ h => FullM7Search.m7DecideSpec_monoX h)
  have rSet64 := mf_base_at m7FidBase_m7Set64_mem
    (hno := fun _ _ _ _ h => FullM7Search.m7Set64Spec_monoX h)
  have rEmaSwap := mf_base_at m7FidBase_emaSwap_mem
    (hno := fun _ _ _ _ h => FullM7Search.m7EmaSwapSpec_monoX h)
  have rProbeTail := mf_base_at rProbeTailMem (hno := fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
  have rProbe := mf_base_at rProbeMem (hno := fun _ _ _ _ h => FullM6Orch.m6ProbeSpec_monoX h)
  have rInit := mf_extra_at (Γ := m7FidBaseEnv) 0 "m6_hdr_init" [i64] [] m6HdrInitSpec rfl
    (fun _ _ _ _ h => m6HdrInitSpec_monoX h)
  have rEnsure := mf_extra_at (Γ := m7FidBaseEnv) 1 "m6_ext_ensure_init" [i64] []
    m6ExtEnsureInitSpec rfl (fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)
  have rOvf := mf_extra_at (Γ := m7FidBaseEnv) 2 "full_prop_lit_ovf_hot" [i64, i32, i32, i32]
    [.bool] FullM7BcpHot.fullPropLitOvfHotSpec rfl
  have rChrono := mf_extra_at (Γ := m7FidBaseEnv) 3 "full_prop_chrono_hot" [i64, i64] [.bool]
    FullM7BcpHot.fullPropChronoHotSpec rfl
  have rHb := mf_extra_at (Γ := m7FidBaseEnv) 4 "full_has_bin" [i64, i32, i32] [.bool]
    Full.fullHasBinSpec rfl
  have rMinMark := mf_extra_at (Γ := m7FidBaseEnv) 5 "full_min_mark" [i64, i32, i8] []
    Full.fullMinMarkSpec rfl
  have rAnaSift := mf_extra_at (Γ := m7FidBaseEnv) 6 "full_ana_sift_m6" [i64, i64, i64, i64, i64]
    [] FullM6MinShrink.m6AnaSiftSpec rfl (fun _ _ _ _ h => FullM6MinShrink.m6AnaSiftSpec_monoX h)
  have rSortAna := mf_extra_at (Γ := m7FidBaseEnv) 7 "full_sort_ana_qs_m6" [i64, i64] []
    FullM6MinShrink.m6SortAnaQsSpec rfl (fun _ _ _ _ h => FullM6MinShrink.m6SortAnaQsSpec_monoX h)
  have rStSift := mf_extra_at (Γ := m7FidBaseEnv) 8 "full_sort_tmp_sift_m7"
    [i64, i64, i64, i64, i64] [] Full.FullMinSpecs.fullSortTmpSiftSpec rfl
  have rStHeap := mf_extra_at (Γ := m7FidBaseEnv) 9 "full_sort_tmp_heap_m7" [i64, i64, i64, i64] []
    FullM7AnalyzeSort.m7SortTmpHeapSpec rfl
    (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpHeapSpec_monoX h)
  have rSortTmp := mf_extra_at (Γ := m7FidBaseEnv) 10 "full_sort_tmp" [i64] []
    FullM7AnalyzeSort.m7SortTmpSpec rfl (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h)
  have rMinDfs := mf_extra_at (Γ := m7FidBaseEnv) 11 "full_min_lit_dfs_m6"
    [i64, i32, .bool, .bool] [.bool] FullM6MinShrink.m6MinLitDfsSpec rfl
    (fun _ _ _ _ h => FullM6MinShrink.m6MinLitDfsSpec_monoX h)
  have rShrLow := mf_extra_at (Γ := m7FidBaseEnv) 12 "full_shrink_lower_m6" [i64, i32, i32] [.bool]
    Full.fullShrinkLowerSpec rfl
  have rShrBlkB := mf_extra_at (Γ := m7FidBaseEnv) 13 "full_shrink_blk_bool_m6"
    [i64, i64, i64, i32, i64] [.bool] FullM6MinShrink.m6ShrinkBlkBoolSpec rfl
    (fun _ _ _ _ h => FullM6MinShrink.m6ShrinkBlkBoolSpec_monoX h)
  have rWlkCb := mf_extra_at (Γ := m7FidBaseEnv) 14 "full_walk_cb_inv_m7" [i64, i64, i64] [i64]
    FullM7Walk.m7CbInvSpec rfl (fun _ _ _ _ h => FullM7Walk.m7CbInvSpec_noExit h)
  have rWlkTbl := mf_extra_at (Γ := m7FidBaseEnv) 15 "full_walk_init_table_m7" [i64, i64] []
    FullM7Walk.m7InitTableSpec rfl (fun _ _ _ _ h => FullM7Walk.m7InitTableSpec_noExit h)
  have rWlkEff := mf_extra_at (Γ := m7FidBaseEnv) 16 "full_walk_effort_m7" [i64, i64] [i64]
    FullM7Walk.m7EffortSpec rfl (fun _ _ _ _ h => FullM7Walk.m7EffortSpec_noExit h)
  have rWlkVals := mf_extra_at (Γ := m7FidBaseEnv) 17 "full_walk_init_vals_m7" [i64] []
    FullM7Walk.m7InitValsSpec rfl (fun _ _ _ _ h => FullM7Walk.m7InitValsSpec_noExit h)
  have rWlkCol := mf_extra_at (Γ := m7FidBaseEnv) 18 "full_walk_collect_m7" [i64] [i64]
    FullM7Walk.m7CollectSpec rfl (fun _ _ _ _ h => FullM7Walk.m7CollectSpec_noExit h)
  have rWlkOcc := mf_extra_at (Γ := m7FidBaseEnv) 19 "full_walk_build_occ_m7" [i64, i64] [i64]
    FullM7Walk.m7BuildOccSpec rfl (fun _ _ _ _ h => FullM7Walk.m7BuildOccSpec_noExit h)
  have rWlkBrk := mf_extra_at (Γ := m7FidBaseEnv) 20 "full_walk_break_m7" [i64, i32, i64] [i32]
    FullM7Walk.m7BreakSpec rfl (fun _ _ _ _ h => FullM7Walk.m7BreakSpec_noExit h)
  have rWlkPick := mf_extra_at (Γ := m7FidBaseEnv) 21 "full_walk_pick_m7" [i64, i32, i64] [i64]
    FullM7Walk.m7PickSpec rfl (fun _ _ _ _ h => FullM7Walk.m7PickSpec_noExit h)
  have rWlkFlip := mf_extra_at (Γ := m7FidBaseEnv) 22 "full_walk_flip_m7" [i64, i32, i64, i64] [i64]
    FullM7Walk.m7FlipSpec rfl (fun _ _ _ _ h => FullM7Walk.m7FlipSpec_noExit h)
  have rWlkSave := mf_extra_at (Γ := m7FidBaseEnv) 23 "full_walk_save_min_m7" [i64, i64, .bool] []
    FullM7Walk.m7SaveMinSpec rfl (fun _ _ _ _ h => FullM7Walk.m7SaveMinSpec_noExit h)
  have rWarmupM7 := mf_extra_at (Γ := m7FidBaseEnv) 24 "full_warmup_m7" [i64] []
    Full.fullWarmupSpec rfl
  have rAb6 := mf_extra_at (Γ := m7FidBaseEnv) 25 "full_add_bin_m6" [i64, i32, i32] [i64]
    FullM6VivBackbone.fullAddBinM6Spec rfl
  have rVivTier := mf_extra_at (Γ := m7FidBaseEnv) 51 _ _ _ _ rfl
    (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)
  have rCompNeed := mf_extra_at (Γ := m7FidBaseEnv) 52 "full_compact_needed" [i64] [.bool]
    FullM4Compact.fullCompactNeededSpec rfl
  have rWalkM7 := mf_extra_at (Γ := m7FidBaseEnv) 53 "full_walk_m7" [i64] [] Full.fullWalkSpec rfl
  have rBumpAna := mf_extra_at (Γ := m7FidBaseEnv) 54 "full_bump_analyzed_m6_hdr" [i64] []
    m6aBumpAnalyzedSpec rfl (fun _ _ _ _ h => m6aBumpAnalyzedSpec_monoX h)
  have rWalkCanon := mf_extra_at (Γ := m7FidBaseEnv) 56 "full_walk" [i64] []
    Full.fullWarmupSpec rfl
  have rBvaMlFid := mf_extra_at (Γ := m7FidBaseEnv) 57 "full_bva_match_large_fid"
    [i64, i32, i32, i32] [.bool] FullM7FidelityCore.fidBvaMatchLargeSpec rfl
    (fun _ _ _ _ h => FullM7FidelityCore.fidBvaMatchLargeSpec_monoX h)
  have rReordSift := mf_extra_at (Γ := m7FidBaseEnv) 58 "full_reorder_sift_fid" [i64, i64, i64] []
    FullM7FidelityCore.fidReorderSiftSpec rfl
    (fun _ _ _ _ h => FullM7FidelityCore.fidReorderSiftSpec_monoX h)
  have rHdrDecFid := mf_extra_at (Γ := m7FidBaseEnv) 59 "m6_hdr_decide_fid" [i64] [i64]
    FullM6Hdr.m6HdrDecideSpec rfl (fun _ _ _ _ h => FullM6Hdr.m6HdrDecideSpec_monoX h)
  have r0 := mf_extra_at (Γ := m7FidBaseEnv) 26 _ _ _ _ rfl
  have r1 := mf_extra_at (Γ := m7FidBaseEnv) 27 _ _ _ _ rfl
  have r2 := mf_extra_at (Γ := m7FidBaseEnv) 28 _ _ _ _ rfl
  have r3 := mf_extra_at (Γ := m7FidBaseEnv) 29 _ _ _ _ rfl
  have r4 := mf_extra_at (Γ := m7FidBaseEnv) 30 _ _ _ _ rfl
  have r5 := mf_extra_at (Γ := m7FidBaseEnv) 31 _ _ _ _ rfl
  have r6 := mf_extra_at (Γ := m7FidBaseEnv) 32 _ _ _ _ rfl
  have r7 := mf_extra_at (Γ := m7FidBaseEnv) 33 _ _ _ _ rfl
  have r8 := mf_extra_at (Γ := m7FidBaseEnv) 34 _ _ _ _ rfl
  have r9 := mf_extra_at (Γ := m7FidBaseEnv) 35 _ _ _ _ rfl
  have r10 := mf_extra_at (Γ := m7FidBaseEnv) 36 _ _ _ _ rfl
  have r11 := mf_extra_at (Γ := m7FidBaseEnv) 37 _ _ _ _ rfl
  have r12 := mf_extra_at (Γ := m7FidBaseEnv) 38 _ _ _ _ rfl
  have r13 := mf_extra_at (Γ := m7FidBaseEnv) 39 _ _ _ _ rfl
  have r14 := mf_extra_at (Γ := m7FidBaseEnv) 40 _ _ _ _ rfl
  have r15 := mf_extra_at (Γ := m7FidBaseEnv) 41 _ _ _ _ rfl
  have r16 := mf_extra_at (Γ := m7FidBaseEnv) 42 _ _ _ _ rfl
  have r17 := mf_extra_at (Γ := m7FidBaseEnv) 43 _ _ _ _ rfl
  have r18 := mf_extra_at (Γ := m7FidBaseEnv) 44 _ _ _ _ rfl
  have r19 := mf_extra_at (Γ := m7FidBaseEnv) 45 _ _ _ _ rfl
  have r20 := mf_extra_at (Γ := m7FidBaseEnv) 46 _ _ _ _ rfl
  have r21 := mf_extra_at (Γ := m7FidBaseEnv) 47 _ _ _ _ rfl
  have r22 := mf_extra_at (Γ := m7FidBaseEnv) 48 _ _ _ _ rfl
  have r23 := mf_extra_at (Γ := m7FidBaseEnv) 49 _ _ _ _ rfl
  have r24 := mf_extra_at (Γ := m7FidBaseEnv) 50 _ _ _ _ rfl
  have hExtraImpl : TableImpl m7FidelityEnv mfExtraBaseFns mfExtraBaseRows := by
    have hCore25 : TableImpl m7FidelityEnv (mfExtraBaseFns.take 25) (mfExtraBaseRows.take 25) := by
      have hf25 : mfExtraBaseFns.take 25 =
          [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
          , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
          , FullM7BcpHot.m7PropLitOvfFn
          , FullM7BcpHot.m7PropChronoFn
          , mfHasBinFn
          , mfMinMarkFn
          , ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [],
              FullM6MinShrink.full_ana_sift_m6_body⟩
          , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.full_sort_ana_qs_m6_body⟩
          , ⟨"full_sort_tmp_sift_m7", [i64, i64, i64, i64, i64], [],
              FullM7AnalyzeSort.full_sort_tmp_sift_m7_body⟩
          , ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [],
              FullM7AnalyzeSort.full_sort_tmp_heap_m7_body⟩
          , ⟨"full_sort_tmp", [i64], [], FullM7AnalyzeSort.full_sort_tmp_m7_body⟩
          , ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
              FullM6MinShrink.full_min_lit_dfs_m6_body⟩
          , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool],
              FullM6MinShrink.full_shrink_lower_m6_body⟩
          , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
              FullM6MinShrink.full_shrink_blk_bool_m6_body⟩
          , ⟨"full_walk_cb_inv_m7", [i64, i64, i64], [i64], FullM7Walk.full_walk_cb_inv_m7_body⟩
          , ⟨"full_walk_init_table_m7", [i64, i64], [], FullM7Walk.full_walk_init_table_m7_body⟩
          , ⟨"full_walk_effort_m7", [i64, i64], [i64], FullM7Walk.full_walk_effort_m7_body⟩
          , ⟨"full_walk_init_vals_m7", [i64], [], FullM7Walk.full_walk_init_vals_m7_body⟩
          , ⟨"full_walk_collect_m7", [i64], [i64], FullM7Walk.full_walk_collect_m7_body⟩
          , ⟨"full_walk_build_occ_m7", [i64, i64], [i64], FullM7Walk.full_walk_build_occ_m7_body⟩
          , ⟨"full_walk_break_m7", [i64, i32, i64], [i32], FullM7Walk.full_walk_break_m7_body⟩
          , ⟨"full_walk_pick_m7", [i64, i32, i64], [i64], FullM7Walk.full_walk_pick_m7_body⟩
          , ⟨"full_walk_flip_m7", [i64, i32, i64, i64], [i64], FullM7Walk.full_walk_flip_m7_body⟩
          , ⟨"full_walk_save_min_m7", [i64, i64, .bool], [],
              FullM7Walk.full_walk_save_min_m7_body⟩
          , ⟨"full_warmup_m7", [i64], [], FullM7Walk.full_warmup_m7_body⟩ ] := by t_kernel_rfl
      rw [hf25]
      dsimp only [mfExtraBaseRows]
      exact ⟨ SpecEntry.Impl.of (m6_hdr_init_wp m7FidelityEnv)
        , SpecEntry.Impl.of (m6_ext_ensure_init_wp m7FidelityEnv rInit)
        , SpecEntry.Impl.of (FullM7BcpHot.full_prop_lit_ovf_hot_wp m7FidelityEnv rWpEnv)
        , SpecEntry.Impl.of (FullM7BcpHot.full_prop_chrono_hot_wp m7FidelityEnv rWdEnv rUnw rWpEnv)
        , SpecEntry.Impl.of (mf_hasBin_wp m7FidelityEnv)
        , SpecEntry.Impl.of (mf_minMark_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6MinShrink.full_ana_sift_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6MinShrink.full_sort_ana_qs_m6_wp m7FidelityEnv rAnaSift)
        , SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_sift_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_heap_m7_wp m7FidelityEnv rStSift)
        , SpecEntry.Impl.of (FullM7AnalyzeSort.full_sort_tmp_m7_wp m7FidelityEnv rStHeap)
        , SpecEntry.Impl.of (FullM6MinShrink.full_min_lit_dfs_m6_wp m7FidelityEnv rMinMark)
        , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_lower_m6_wp m7FidelityEnv rMinMark rMinDfs)
        , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_blk_bool_m6_wp m7FidelityEnv
            rShrLow rMinMark)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_cb_inv_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_init_table_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_effort_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_init_vals_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_collect_m7_wp m7FidelityEnv rNext)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_build_occ_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_break_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_pick_m7_wp m7FidelityEnv rWlkBrk rRng)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_flip_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_walk_save_min_m7_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM7Walk.full_warmup_m7_wp m7FidelityEnv rNDV rAsg rProp rBt)
        , trivial ⟩
    have hAbImpl : TableImpl m7FidelityEnv (FullM6VivBackbone.m6VivBackbone_fns.take 1)
        (FullM6VivBackbone.m6VivBackboneSpecTable.take 1) := by
      rw [show FullM6VivBackbone.m6VivBackbone_fns.take 1 =
          [⟨"full_add_bin_m6", [i64, i32, i32], [i64],
            FullM6VivBackbone.full_add_bin_m6_body⟩] from rfl]
      exact ⟨SpecEntry.Impl.of
        (FullM6VivBackbone.full_add_bin_m6_ext_wp m7FidelityEnv rHb rALvl rWpEnv), trivial⟩
    have hVivImpl : TableImpl m7FidelityEnv ((FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25)
        ((FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25) := by
      rw [show (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 =
          [ ⟨"full_viv_unreason_m6", [i64, i32], [], FullM6VivBackbone.full_viv_unreason_m6_body⟩
          , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_watch_rank_m6_body⟩
          , ⟨"full_viv_best_watch_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_best_watch_m6_body⟩
          , ⟨"full_viv_simplify_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_simplify_m6_body⟩
          , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64],
              FullM6VivBackbone.full_viv_commit_m6_body⟩
          , ⟨"full_viv_mark_garb_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_mark_garb_m6_body⟩
          , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_bin_m6_body⟩
          , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_subsumes_cl_m6_body⟩
          , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32],
              FullM6VivBackbone.full_viv_deduce_m6_body⟩
          , ⟨"full_viv_best_implied_m6", [i64, i32], [i32],
              FullM6VivBackbone.full_viv_best_implied_m6_body⟩
          , ⟨"full_viv_reestablish_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_reestablish_m6_body⟩
          , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_inst_check_m6_body⟩
          , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_inst_m6_body⟩
          , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
              FullM6VivBackbone.full_viv_finish_m6_body⟩
          , ⟨"full_viv_sort_counts_m6", [i64, i32], [],
              FullM6VivBackbone.full_viv_sort_counts_m6_body⟩
          , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool],
              FullM6VivBackbone.full_viv_has_l0_m6_body⟩
          , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64],
              FullM6VivBackbone.full_viv_l0_simp_m6_body⟩
          , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [],
              FullM6VivBackbone.full_viv_reuse_prefix_m6_body⟩
          , ⟨"full_viv_clause_m6", [i64, i32], [i64],
              FullM6VivBackbone.full_viv_clause_m6_body⟩
          , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
              FullM6VivBackbone.full_viv_tier_match_m6_body⟩
          , ⟨"full_viv_collect_m6", [i64, i64], [i64],
              FullM6VivBackbone.full_viv_collect_m6_body⟩
          , ⟨"full_viv_count_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_count_m6_body⟩
          , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.full_viv_keys_m6_body⟩
          , ⟨"full_viv_sort_sched_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_sort_sched_m6_body⟩
          , ⟨"full_viv_clear_tier_m6", [i64, i64], [],
              FullM6VivBackbone.full_viv_clear_tier_m6_body⟩ ] from rfl]
      exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_viv_unreason_m6_wp m7FidelityEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_watch_rank_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_watch_m6_wp m7FidelityEnv r1)
        , SpecEntry.Impl.of
            (FullM6VivBackbone.full_viv_simplify_m6_wp m7FidelityEnv rUnw rAu rAb6 rWpEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_commit_m6_wp m7FidelityEnv
            rBt rUnw rAu rAb6 rWpEnv r0 r2)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_mark_garb_m6_wp m7FidelityEnv r0 rUnw)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_bin_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_cl_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_deduce_m6_wp m7FidelityEnv r6 r7)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_implied_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reestablish_m6_wp m7FidelityEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_check_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_m6_wp m7FidelityEnv
            rBt rAsg rPI r8 r11 r4)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_finish_m6_wp m7FidelityEnv
            r8 r5 rBt r4 r10 r12)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_counts_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_has_l0_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_l0_simp_m6_wp m7FidelityEnv r15 rBt r3)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reuse_prefix_m6_wp m7FidelityEnv rBt)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clause_m6_wp m7FidelityEnv
            r16 r14 r17 r9 rAsg rPI rBt r13)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_tier_match_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_collect_m6_wp m7FidelityEnv rNext r19)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_count_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_keys_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_sched_m6_wp m7FidelityEnv)
        , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clear_tier_m6_wp m7FidelityEnv rNext r19)
        , trivial ⟩
    have hfSplit : mfExtraBaseFns =
        (mfExtraBaseFns.take 25 ++ FullM6VivBackbone.m6VivBackbone_fns.take 1) ++
          (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 25 := by t_kernel_rfl
    have hrSplit : mfExtraBaseRows =
        (mfExtraBaseRows.take 25 ++ FullM6VivBackbone.m6VivBackboneSpecTable.take 1) ++
          (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25 := by t_kernel_rfl
    rw [hfSplit, hrSplit]
    exact tableImpl_append (by t_kernel_rfl) (tableImpl_append (by t_kernel_rfl) hCore25 hAbImpl)
      hVivImpl
  have hnotExtra : ∀ (nm : Sym) {as bs xs m Q X}, nm ∉ mfExtraRows.map SpecEntry.name →
      Env.ofTable mfExtraRows nm as bs xs m Q X → False := by
    intro _ _ _ _ _ _ _ hni he; exact hni (mf_ofTable_name_mem he)
  have hTailWp := mfOrchTail_wp m7FidelityEnv
    rLuckyLate
    (mf_base_at hc1Tail.1 (hno := fun _ _ _ _ h => fullM6MemInitExactSpec_monoX h))
    (mf_base_at (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.parseBody))
    rProp
    rAnalyzeM6
    rReduceM6
    rSwitchMode
    rRstDue
    rRst
    rReorderM6
    rRephase
    (mf_base_at rPreM6Mem (hno := fun _ _ _ _ h => fullM6PreprocessSpec_monoX h))
    rSimpM6
    rDecideM7
    (mf_base_at hc2.extend)
    (mf_base_at hc1Tail.2)
    (mf_base_at m7FidBase_searchM6_mem (hno := fun _ _ _ _ h => fullM6SearchSpec_monoX h))
    (mf_base_at (m7FidBase_tail_mem _ (m7FidOrchTail_solve_mem m7FidSolveBytesSpec).1)
      (hno := fun _ _ _ _ h => m7FidSolveBytesSpec_monoX h))
  have hwfOrig : ∀ f ∈ m7Module.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hbaseOk.fnsOk pre f post hsplit).1
  have hMidOk : ModuleOk mfMidEnv m7Module := by
    refine LeanQbe.T.Module.moduleOk_of_checkAcyclic m7_acyclic hwfOrig ?_
    intro g hg xs m Q X hrow
    rcases hrow with ⟨hnbad, hb⟩
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    have ⟨hwfG, hcallsG, hwpG⟩ := hbaseOk.fnsOk pre g post hsplit
    have hnoBad : mfNoCallBad
        (g.body (fun _ => Unit) (fun _ => Unit) (Tup.units g.as)) = true :=
      List.all_eq_true.mp mf_all_nonbad_no_bad g (List.mem_filter.mpr ⟨hg, hnbad⟩)
    exact wp_env_agree_of_callsOk
      (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
      (mf_callsOk_filter _ hcallsG hnoBad)
      (fun f as bs hmem' _ _ _ _ hc => ⟨(List.mem_filter.mp hmem').2, hc⟩)
      m (hwpG xs m Q X hb)
  refine mfPatchModule_moduleOk hMidOk m7Fidelity_acyclic m7FidRepls_wf m7FidBefores_wf ?_ ?_ ?_ ?_
  · intro f _ _ _ _ _ _ ⟨hok, hb⟩
    exact M7FidelityEnv.base (mf_not_excl_of_ok hok) hb
  · intro g hg hfind
    change g ∈ m7Fns at hg
    have hneViv : g.name ≠ "full_vivify_m6_hdr" := mf_ne_of_find_none (r0 := m7pVivifyFn)
      (by simp [m7FidRepls, m7ParityVivTiersPatchFns]) hfind
    have hneVt : g.name ≠ "full_vivify_tier_m6_hdr" := mf_ne_of_find_none (r0 := m7pVivifyTierFn)
      (by simp [m7FidRepls, m7ParityVivTiersPatchFns]) hfind
    have hneCn : g.name ≠ "full_compact_needed" := mf_ne_of_find_none (r0 := m7fixCompactNeededFn)
      (by simp [m7FidRepls, m7FidHeadRepls]) hfind
    have hneWlk : g.name ≠ "full_walk_m7" := mf_ne_of_find_none
      (r0 := FullM7FidelityCore.fidWalkM7Fn)
      (by simp [m7FidRepls, FullM7FidelityCore.fidCorePatchFns]) hfind
    have hneBa : g.name ≠ "full_bump_analyzed_m6_hdr" := mf_ne_of_find_none
      (r0 := FullM7FidelitySearch.fidBumpAnalyzedFn)
      (by simp [m7FidRepls, FullM7FidelitySearch.fidSearchPatchRepls]) hfind
    have hnePt : g.name ≠ "full_probe_tail_m6" := mf_ne_of_find_none
      (r0 := FullM7FidelitySchedFix.fid2ProbeTailM6Fn)
      (by simp [m7FidRepls, FullM7FidelitySchedFix.fidSchedFixPatchFns,
        FullM7FidelitySchedFix.fidSchedFixFns_eq_patchFns]) hfind
    have hnePm : g.name ≠ "full_probe_m6" := mf_ne_of_find_none
      (r0 := FullM7FidelitySchedFix.fid2ProbeM6Fn)
      (by simp [m7FidRepls, FullM7FidelitySchedFix.fidSchedFixPatchFns,
        FullM7FidelitySchedFix.fidSchedFixFns_eq_patchFns]) hfind
    have hnePre : g.name ≠ "full_preprocess_m6" := mf_ne_of_find_none
      (r0 := FullM7FidelitySchedFix.fid2PreprocessM6Fn)
      (by simp [m7FidRepls, FullM7FidelitySchedFix.fidSchedFixPatchFns,
        FullM7FidelitySchedFix.fidSchedFixFns_eq_patchFns]) hfind
    have hneSrch : g.name ≠ "full_search_m6" := mf_ne_of_find_none
      (r0 := FullM7FidelitySearch.fidSearchM6Fn)
      (by simp [m7FidRepls, FullM7FidelitySearch.fidSearchPatchRepls]) hfind
    by_cases h119 : g.name = "full_restore_bump_ana_m6_hdr"
    · refine Or.inl fun xs m Q X hrow => ?_
      have hgeq : g = m6aRestoreBumpAnaM6HdrFn :=
        fn_eq_of_mem_idx m7_names_nodup hg mf_idx_119 h119
      subst hgeq
      cases hrow with
      | base _ hb =>
        exact full_restore_bump_ana_m6_hdr_wp m7FidelityEnv rBumpAna rClearAna xs m Q X
          (m6aRestoreBumpAnaSpec_monoX (m7FidBase_elim_of_mem hc2p.restoreBumpAna hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · by_cases h120 : g.name = "full_ana_failed_lit_m6_hdr"
      · refine Or.inl fun xs m Q X hrow => ?_
        have hgeq : g = m6aAnaFailedLitM6HdrFn :=
          fn_eq_of_mem_idx m7_names_nodup hg mf_idx_120 h120
        subst hgeq
        cases hrow with
        | base _ hb =>
          exact full_ana_failed_lit_m6_hdr_wp m7FidelityEnv rClearAna rBumpAna rBt rALvl xs m Q X
            (m6aAnaFailedLitSpec_monoX (m7FidBase_elim_of_mem hc2p.anaFailedLit hb))
        | extra he => exact False.elim (hnotExtra _ (by decide) he)
      · by_cases h150 : g.name = "full_analyze_core_m6"
        · refine Or.inl fun xs m Q X hrow => ?_
          have hgeq : g = m6oAnalyzeCoreM6Fn :=
            fn_eq_of_mem_idx m7_names_nodup hg mf_idx_150 h150
          subst hgeq
          cases hrow with
          | base _ hb =>
            exact full_analyze_core_m6_m7_wp m7FidelityEnv rOneLit rAnaFailed rDed1uip rRstBump
              rMinShr rTickRel rEmaUpd rLrnCl xs m Q X
              (m6HdrAnalyzeSpec_monoX (m7FidBase_elim_of_mem rAnaCoreMem hb))
          | extra he => exact False.elim (hnotExtra _ (by decide) he)
        · by_cases h151 : g.name = "full_analyze_m6_hdr"
          · refine Or.inl fun xs m Q X hrow => ?_
            have hgeq : g = m6aAnalyzeM6HdrFn :=
              fn_eq_of_mem_idx m7_names_nodup hg mf_idx_151 h151
            subst hgeq
            cases hrow with
            | base _ hb =>
              exact full_analyze_m6_hdr_wp m7FidelityEnv rUpdTier rDrUpd rAnaCore xs m Q X
                (m6HdrAnalyzeSpec_monoX (m7FidBase_elim_of_mem hc2.analyzeM6 hb))
            | extra he => exact False.elim (hnotExtra _ (by decide) he)
          · by_cases h166 : g.name = "full_walk_warmup_m7"
            · refine Or.inl fun xs m Q X hrow => ?_
              have hgeq : g = ⟨"full_walk_warmup_m7", [i64], [],
                  FullM7Walk.full_walk_warmup_m7_body⟩ :=
                fn_eq_of_mem_idx m7_names_nodup hg mf_idx_166 h166
              subst hgeq
              cases hrow with
              | base hne _ => exact absurd (by decide) hne
              | extra he =>
                have hspec : Full.fullWarmupSpec xs m Q X :=
                  mf_extra_elim (List.mem_of_getElem? (i := 55) rfl) he
                exact FullM7Walk.full_walk_warmup_m7_wp m7FidelityEnv rWarmupM7 rWalkM7 xs m Q X
                  hspec
            · by_cases h168 : g.name = "full_walk"
              · refine Or.inl fun xs m Q X hrow => ?_
                have hgeq : g = ⟨"full_walk", [i64], [],
                    FullM7Walk.full_walk_warmup_m7_body⟩ :=
                  fn_eq_of_mem_idx m7_names_nodup hg mf_idx_168 h168
                subst hgeq
                cases hrow with
                | base hne _ => exact absurd (by decide) hne
                | extra he =>
                  have hspec : Full.fullWarmupSpec xs m Q X :=
                    mf_extra_elim (List.mem_of_getElem? (i := 56) rfl) he
                  exact FullM7Walk.full_walk_warmup_m7_wp m7FidelityEnv rWarmupM7 rWalkM7 xs m Q X
                    hspec
              · by_cases h169 : g.name = "full_rephase"
                · refine Or.inl fun xs m Q X hrow => ?_
                  have hgeq : g = FullM7AnalyzeSort.m7RephaseFn :=
                    fn_eq_of_mem_idx m7_names_nodup hg mf_idx_169 h169
                  subst hgeq
                  cases hrow with
                  | base _ hb =>
                    exact FullM7SpecBridges.full_rephase_m7_warmup_searchLog_wp m7FidelityEnv
                      rBt rWalkCanon rLog10 xs m Q X
                      (m7RephaseSpec_monoX (m7FidBase_elim_of_mem hc2.rephase hb))
                  | extra he => exact False.elim (hnotExtra _ (by decide) he)
                · by_cases h404 : g.name = "full_simplify_m6"
                  · refine Or.inl fun xs m Q X hrow => ?_
                    have hgeq : g = m6oSimplifyM6Fn :=
                      fn_eq_of_mem_idx m7_names_nodup hg mf_idx_404 h404
                    subst hgeq
                    cases hrow with
                    | base _ hb =>
                      exact full_simplify_m6_compact_wp m7FidelityEnv rBt rProbe rElimM6 rCompNeed
                        rCompact xs m Q X
                        (fullM6SimplifySpec_monoX (m7FidBase_elim_of_mem rSimpM6Mem hb))
                    | extra he => exact False.elim (hnotExtra _ (by decide) he)
                  · by_cases h406 : g.name = "kissat_solve_bytes_m6"
                    · refine Or.inl fun xs m Q X hrow => ?_
                      have hgeq : g = FullM6Orch.m6oSolveBytesM6Fn :=
                        fn_eq_of_mem_idx m7_names_nodup hg mf_idx_406 h406
                      subst hgeq
                      cases hrow with
                      | base _ hb =>
                        exact hTailWp.2.1 xs m Q X (m7FidSolveBytesSpec_monoX
                          (m7FidBase_elim_of_mem
                            (m7FidBase_tail_mem _
                              (m7FidOrchTail_solve_mem m7FidSolveBytesSpec).1) hb))
                      | extra he => exact False.elim (hnotExtra _ (by decide) he)
                    · by_cases h407 : g.name = "full_preprocess"
                      · refine Or.inl fun xs m Q X hrow => ?_
                        have hgeq : g = ⟨"full_preprocess", [i64], [i64],
                            FullM6Orch.full_preprocess_body⟩ :=
                          fn_eq_of_mem_idx m7_names_nodup hg mf_idx_407 h407
                        subst hgeq
                        cases hrow with
                        | base _ hb =>
                          exact hTailWp.2.2.1 xs m Q X (fullM6PreprocessSpec_monoX
                            (m7FidBase_elim_of_mem m7FidBase_preprocess_mem hb))
                        | extra he => exact False.elim (hnotExtra _ (by decide) he)
                      · by_cases h408 : g.name = "full_search"
                        · refine Or.inl fun xs m Q X hrow => ?_
                          have hgeq : g = ⟨"full_search", [i64], [i64],
                              FullM6Orch.full_search_body⟩ :=
                            fn_eq_of_mem_idx m7_names_nodup hg mf_idx_408 h408
                          subst hgeq
                          cases hrow with
                          | base _ hb =>
                            exact hTailWp.2.2.2.1 xs m Q X (fullM6SearchSpec_monoX
                              (m7FidBase_elim_of_mem m7FidBase_search_mem hb))
                          | extra he => exact False.elim (hnotExtra _ (by decide) he)
                        · by_cases h409 : g.name = "kissat_solve_bytes"
                          · refine Or.inl fun xs m Q X hrow => ?_
                            have hgeq : g = FullM6Orch.m6oSolveBytesFn :=
                              fn_eq_of_mem_idx m7_names_nodup hg mf_idx_409 h409
                            subst hgeq
                            cases hrow with
                            | base _ hb =>
                              exact hTailWp.2.2.2.2 xs m Q X (m7FidSolveBytesSpec_monoX
                                (m7FidBase_elim_of_mem
                                  (m7FidBase_tail_mem _
                                    (m7FidOrchTail_solve_mem m7FidSolveBytesSpec).2) hb))
                            | extra he => exact False.elim (hnotExtra _ (by decide) he)
                          · have hneIns1 : g.name ≠ "full_bva_match_large_fid" := fun heq =>
                              m7Fns_not_mem_bml (heq ▸ List.mem_map_of_mem hg)
                            have hneIns2 : g.name ≠ "full_reorder_sift_fid" := fun heq =>
                              m7Fns_not_mem_sift (heq ▸ List.mem_map_of_mem hg)
                            have hneIns3 : g.name ≠ "m6_hdr_decide_fid" := fun heq =>
                              m7Fns_not_mem_hdec (heq ▸ List.mem_map_of_mem hg)
                            have hok_g : mfOkName g.name = true := by
                              simp [mfOkName, mfBadNames, Ne.symm hneVt, Ne.symm hneViv,
                                Ne.symm hneCn, Ne.symm hneWlk, Ne.symm hneBa, Ne.symm h119,
                                Ne.symm h120, Ne.symm h150, Ne.symm h151, Ne.symm h166,
                                Ne.symm h168, Ne.symm h169, Ne.symm hnePt, Ne.symm hnePm,
                                Ne.symm hnePre, Ne.symm h404, Ne.symm hneSrch, Ne.symm h406,
                                Ne.symm h407, Ne.symm h408, Ne.symm h409, Ne.symm hneIns1,
                                Ne.symm hneIns2, Ne.symm hneIns3]
                            by_cases hex : g.name ∈ mfExtraBaseRows.map SpecEntry.name
                            · refine Or.inl fun xs m Q X hrow => ?_
                              cases hrow with
                              | base _ hb =>
                                obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
                                have ⟨hwfG, hcallsG, hwpG⟩ := hbaseOk.fnsOk pre g post hsplit
                                have hnoBad : mfNoCallBad
                                    (g.body (fun _ => Unit) (fun _ => Unit) (Tup.units g.as)) =
                                    true :=
                                  List.all_eq_true.mp mf_all_nonbad_no_bad g
                                    (List.mem_filter.mpr ⟨hg, hok_g⟩)
                                exact wp_env_agree_of_callsOk
                                  (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs
                                    (Tup.units g.as))
                                  (mf_callsOk_filter _ hcallsG hnoBad)
                                  (fun f as bs hmem' _ _ _ _ hc => by
                                    have hfl := (List.mem_filter.mp hmem').2
                                    exact M7FidelityEnv.base (mf_not_excl_of_ok hfl) hc)
                                  m (hwpG xs m Q X hb)
                              | extra he =>
                                have hm_n := mf_ofTable_name_mem he
                                have hbase_mem : g.name ∈ mfExtraBaseRows.map SpecEntry.name := by
                                  simpa [mfExtraRows, List.map_append, hneVt, hneCn, hneWlk, hneBa,
                                    h166, h168, hneIns1, hneIns2, hneIns3] using hm_n
                                rcases List.mem_map.mp hbase_mem with ⟨r, hr, hnm⟩
                                rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
                                have hlen_e : mfExtraBaseFns.length = mfExtraBaseRows.length := by
                                  have hl := congrArg List.length mf_extraBaseFns_sigs
                                  simpa only [List.length_map] using hl.symm
                                have hidx_f : idx < mfExtraBaseFns.length := hlen_e ▸ hidx
                                have hf_idx : mfExtraBaseFns[idx]'hidx_f ∈ mfExtraBaseFns :=
                                  List.getElem_mem hidx_f
                                have hsig_eq : (mfExtraBaseRows[idx].name, mfExtraBaseRows[idx].as,
                                    mfExtraBaseRows[idx].rs) =
                                    (mfExtraBaseFns[idx]'hidx_f).sig := by
                                  have hopt := congrArg (fun l => l[idx]?) mf_extraBaseFns_sigs
                                  rw [List.getElem?_map, List.getElem?_eq_getElem hidx,
                                    List.getElem?_map, List.getElem?_eq_getElem hidx_f] at hopt
                                  exact Option.some.inj hopt
                                have hfn_eq_name : (mfExtraBaseFns[idx]'hidx_f).name = g.name :=
                                  (congrArg Prod.fst hsig_eq).symm.trans hnm
                                have hg_eq : g = mfExtraBaseFns[idx]'hidx_f := by
                                  have hm1 := mf_extraBaseFns_sub _ hf_idx
                                  rcases List.mem_iff_getElem.mp hg with ⟨i1, hi1, rfl⟩
                                  rcases List.mem_iff_getElem.mp hm1 with ⟨i2, hi2, heq2⟩
                                  have heq_idx : i1 = i2 := idx_eq_of_name_nodup m7_names_nodup
                                    (List.getElem?_eq_getElem hi2) (List.getElem?_eq_getElem hi1)
                                    (by rw [heq2]; exact hfn_eq_name.symm)
                                  subst heq_idx
                                  exact heq2
                                subst hg_eq
                                have hImpl_idx : SpecEntry.Impl m7FidelityEnv
                                    (mfExtraBaseFns[idx]'hidx_f) (mfExtraBaseRows[idx]'hidx) :=
                                  mf_tableImpl_getElem idx hidx_f hidx hExtraImpl
                                have r_in_extra : mfExtraBaseRows[idx] ∈ mfExtraRows :=
                                  List.mem_append_left _ (List.getElem_mem hidx)
                                rcases hImpl_idx with ⟨⟨hn, ha, hr_⟩, hwp⟩
                                exact hwp xs m Q X (mf_extra_elim_cast r_in_extra hn ha hr_ he)
                            · refine Or.inr fun xs m Q X hrow => ?_
                              cases hrow with
                              | base _ hb => exact ⟨hok_g, hb⟩
                              | extra he =>
                                have hni : g.name ∉ mfExtraRows.map SpecEntry.name := by
                                  simpa [mfExtraRows, List.map_append, hneVt, hneCn, hneWlk, hneBa,
                                    h166, h168, hneIns1, hneIns2, hneIns3] using hex
                                exact False.elim (hnotExtra _ hni he)
  · intro r hr xs m Q X hrow
    rw [m7FidRepls, FullM7FidelitySchedFix.fidSchedFixPatchFns,
      FullM7FidelitySchedFix.fidSchedFixFns_eq_patchFns] at hr
    simp only [m7FidHeadRepls, m7ParityVivTiersPatchFns, FullM7FidelityCore.fidCorePatchFns,
      FullM7FidelitySearch.fidSearchPatchRepls,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl)
    · cases hrow with
      | base _ hb =>
        exact full_bva_commit_m7_wp m7FidelityEnv rWdEnv rInitFresh rAddBinCan rAllocCl rWpEnv
          rDelBin rUnw xs m Q X (m7FidBase_elim_of_mem m7FidBase_bvaCommit_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_analyze_rsn_m7_wp m7FidelityEnv rAnaLit xs m Q X
          (m7FidBase_elim_of_mem hc2gu.2 hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : FullM4Compact.fullCompactNeededSpec xs m Q X :=
          mf_extra_elim (List.mem_of_getElem? (i := 52) rfl) he
        exact full_compact_needed_m7fix_wp m7FidelityEnv xs m Q X hspec
    · cases hrow with
      | base _ hb =>
        exact full_compact_mark_live_m7fix_wp m7FidelityEnv rNext xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_compactMarkLive_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_compact_vars_m7fix_wp m7FidelityEnv xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_compactVars_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_sweep_copy_m7fix_wp m7FidelityEnv rALvl rWpEnv xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_sweepCopy_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact m7Fid_forward_sub_wp m7FidelityEnv rDedup rFlushUnits rColSort rFlushLg rCheckCl
          rConnSub rNext rReconn xs m Q X
          (m7FidBase_elim_of_mem (m7FidBase_bve_mem _ m7FidBveRows_specs.fwdSub) hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySched.full_ilog10_fid_wp m7FidelityEnv xs m Q X
          (m7FidBase_elim_of_mem hc1.ilog10 hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySched.full_calc_max_v_fid_wp m7FidelityEnv rFixedBytes xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_calcMaxV_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact m6_hdr_sync_legacy_tiers_wp m7FidelityEnv rEnsure xs m Q X
          (m6HdrW2aSpec_monoX (m7FidBase_elim_of_mem hc1.hdrSyncLegacy hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_propagate_ignore_hot_wp m7FidelityEnv rOvf rChrono xs m Q X
          (m7FidBase_elim_of_mem hc1.propIgnoreHot hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_propagate_ignore_canon_hot_wp m7FidelityEnv rOvf rChrono xs m Q X
          (m7FidBase_elim_of_mem hc1.propagateIgn hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : m6aVivifyTierSpec xs m Q X :=
          m6aVivifyTierSpec_monoX (mf_extra_elim (List.mem_of_getElem? (i := 51) rfl) he)
        exact FullM7ParityVivTiers.full_vivify_tier_m6_hdr_wp m7FidelityEnv rBt r20 r21 r22 r23 r18
          rPropS15 r24 xs m Q X hspec
    · cases hrow with
      | base _ hb =>
        exact FullM7ParityVivTiers.full_vivify_m6_hdr_wp m7FidelityEnv rBt rSync rGetWm rVivTier
          xs m Q X (m6aVivifySpec_monoX (m7FidBase_elim_of_mem hc2p.vivifyM6Hdr hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySchedFix.full_reduce_fid2_wp m7FidelityEnv rIsqrt rLog10 rNext rRecomp
          rSetWm rMrkRsn rSortReds rBt rPropS15 rArSwp xs m Q X
          (m6ReduceSpec_monoX (m7FidBase_elim_of_mem rReduceM6Mem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySchedFix.full_eliminate_fid2_wp m7FidelityEnv rElimDticks rLog10
          rScaleD rEnterDense rMinU64 rFwdSub rElimBve rRebuild xs m Q X
          (m7FidBase_elim_of_mem (m7FidBase_bve_mem _ m7FidBveRows_specs.eliminateM6) hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySchedFix.full_probe_tail_fid2_wp m7FidelityEnv rBackbone rTrans xs m Q X
          (m6ProbeTailSpec_monoX (m7FidBase_elim_of_mem rProbeTailMem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySchedFix.full_probe_fid2_wp m7FidelityEnv rDticks rLog10 rScaleM5
          rVivM6 rEnterDense rDelay rCongDense rRebuild rSetWm rRedD rBumpD rSwpDense rSubst
          rProbeTail rBackbone rMinU64 rFactor xs m Q X
          (FullM6Orch.m6ProbeSpec_monoX (m7FidBase_elim_of_mem rProbeMem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact full_preprocess_fid2_compact_wp m7FidelityEnv rPropS15 rArSwp rLucky rCompNeed
          rCompact rScaleM5 rProbe xs m Q X
          (fullM6PreprocessSpec_monoX (m7FidBase_elim_of_mem rPreM6Mem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_min_shrink_fid_wp m7FidelityEnv rSortTmp rMinMark rMinDfs
          rShrBlkB xs m Q X
          (FullM7SpecBridges.m7MinShrinkSpec_monoX (m7FidBase_elim_of_mem hc2p.minShrinkM6 hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_bva_scan_cands_fid_wp m7FidelityEnv xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_bvaScanCands_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_bva_filter_row_fid_wp m7FidelityEnv rBvaMlFid xs m Q X
          (m7FidBase_elim_of_mem m7FidBase_bvaFilterRow_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_reorder_queue_fid_wp m7FidelityEnv rNext rRescale rHeapUp
          rReordSift xs m Q X (m7FidBase_elim_of_mem hc3p.reorderQueueM7 hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_reorder_fid_wp m7FidelityEnv rReorderQ xs m Q X
          (m7FidBase_elim_of_mem rReorderM6Mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelityCore.full_elim_bve_fid_wp m7FidelityEnv rFlushUnits rBvePush rBvePop
          rBveNbrs rBveVar xs m Q X (m7FidBase_elim_of_mem m7FidBase_elimBveM7_mem hb)
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : Full.fullWalkSpec xs m Q X :=
          mf_extra_elim (List.mem_of_getElem? (i := 53) rfl) he
        exact FullM7FidelityCore.full_walk_fid_wp m7FidelityEnv rWlkVals rWlkCol rWlkCb rWlkTbl
          rWlkOcc rWlkEff rWlkPick rWlkFlip rWlkSave rRng xs m Q X hspec
    · cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : m6aBumpAnalyzedSpec xs m Q X :=
          m6aBumpAnalyzedSpec_monoX (mf_extra_elim (List.mem_of_getElem? (i := 54) rfl) he)
        exact FullM7FidelitySearch.full_bump_analyzed_fid_wp m7FidelityEnv rDrAllow rSortAna
          rQueueMtf rBumpVar rBumpDecay xs m Q X hspec
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySearch.full_switch_mode_fid_wp m7FidelityEnv rIlog rHeapDown rEmaSwap
          rLog10 rSet64 xs m Q X
          (FullM7Search.m7SwitchModeSpec_monoX (m7FidBase_elim_of_mem hc3.switchModeM7 hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
    · cases hrow with
      | base _ hb =>
        exact FullM7FidelitySearch.full_search_fid_wp m7FidelityEnv rLuckyLate rProp rAnalyzeM6
          rReduceM6 rSwitchMode rRstDue rRst rReorderM6 rRephase rSimpM6 rHdrDecFid xs m Q X
          (fullM6SearchSpec_monoX (m7FidBase_elim_of_mem m7FidBase_searchM6_mem hb))
      | extra he => exact False.elim (hnotExtra _ (by decide) he)
  · intro p hp b hb xs m Q X hrow
    simp only [m7FidBefores, FullM7FidelityCore.fidCorePatchBefores,
      FullM7FidelitySearch.fidSearchPatchBefores, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | rfl
    · simp only [List.mem_singleton] at hb; subst hb
      cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : FullM7FidelityCore.fidBvaMatchLargeSpec xs m Q X :=
          FullM7FidelityCore.fidBvaMatchLargeSpec_monoX
            (mf_extra_elim (List.mem_of_getElem? (i := 57) rfl) he)
        exact FullM7FidelityCore.full_bva_match_large_fid_wp m7FidelityEnv xs m Q X hspec
    · simp only [List.mem_singleton] at hb; subst hb
      cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : FullM7FidelityCore.fidReorderSiftSpec xs m Q X :=
          FullM7FidelityCore.fidReorderSiftSpec_monoX
            (mf_extra_elim (List.mem_of_getElem? (i := 58) rfl) he)
        exact FullM7FidelityCore.full_reorder_sift_fid_wp m7FidelityEnv xs m Q X hspec
    · simp only [List.mem_singleton] at hb; subst hb
      cases hrow with
      | base hne _ => exact absurd (by decide) hne
      | extra he =>
        have hspec : FullM6Hdr.m6HdrDecideSpec xs m Q X :=
          FullM6Hdr.m6HdrDecideSpec_monoX (mf_extra_elim (List.mem_of_getElem? (i := 59) rfl) he)
        exact FullM7FidelitySearch.m6_hdr_decide_fid_wp m7FidelityEnv rDecideM7 rDrInit xs m Q X
          hspec

theorem m7Fidelity_solveBytes_mem : FullM6Orch.m6oSolveBytesFn ∈ m7FidelityModule.fns := by
  unfold m7FidelityModule m7FidelityFns
  refine mfPatchFns_mem_of_ne m7oSolveBytesFn_mem fun r hr => ?_
  rw [m7FidRepls, FullM7FidelitySchedFix.fidSchedFixPatchFns,
    FullM7FidelitySchedFix.fidSchedFixFns_eq_patchFns] at hr
  simp only [m7FidHeadRepls, m7ParityVivTiersPatchFns, FullM7FidelityCore.fidCorePatchFns,
    FullM7FidelitySearch.fidSearchPatchRepls, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl) <;> decide

/-- Top-level UNSAT-only `kissat_solve_bytes` soundness theorem for `m7FidelityModule` (`413` fns)
under closed `m7FidelityEnv` (`0` hooks, zero SAT model proofs). -/
theorem m7Fidelity_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m7FidelityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Fidelity_solveBytes_mem
  have hfn := (m7Fidelity_moduleOk.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hmem
  exact ⟨hdom, h20, hmem⟩

/-- Host-framed machine-memory UNSAT lift for `m7FidelityModule`
(`(Eq m' ⋆ F_host) st_dmem`). -/
theorem m7Fidelity_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  ⟨hq.1, hq.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hq.2.2) hdmem⟩

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7FidelityModule` on `8,192 B` `nvM6UnsatInitMem` (`0` SAT model proofs). -/
theorem m7Fidelity_unsat_nv :
    Func.wp m7FidelityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m7Fidelity_solveBytes_mem
  have hfn := (m7Fidelity_moduleOk.fnsOk pre _ post hsplit).2.2
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ _ _ (fun _ _ _ _ => False)
    (m7FidelityEnv_solve_bytes (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM7Fidelity

abbrev m7f_len := @LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityFns_length
abbrev m7f_nx := @LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7Fidelity_noExit
abbrev m7f_mod := @LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7Fidelity_moduleOk
abbrev m7f_nv := @LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7Fidelity_unsat_nv
