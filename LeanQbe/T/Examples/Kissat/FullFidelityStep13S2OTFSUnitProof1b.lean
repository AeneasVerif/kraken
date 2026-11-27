/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof1a
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1

/-!
# Kissat Fidelity Step 13 `full_learn_clause_m6` Main WP Proof (`1b`)

Plain `public section` (`0` `@[expose]`, `0` `import all`, `<= 100` cols, every theorem
`<= 240`L):
1. `s13_learn_unit_wp`: `tmp_len == 1` unit chrono-BT (`full_det_new_level`,
   `full_backtrack_ac_fid`, `full_assign_lvl`, `iterating = 1` when `!probing`,
   `full_eager_subsume`).
2. `s13_learn_pre_gc_wp` & `s13_learn_retry_step_wp`: pre-add headroom GC check and 3-step
   `defrag` / `full_reduce_m6(h, true)` / `full_reduce_purge_c0(h)` retry ladder.
3. `full_learn_clause_m6_step13_wp`: certifies `full_learn_clause_m6` against
   `step13LearnClauseM6Spec` (no `tlen > 2` reverse phase, binary `jumpreasons`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open Kraken.Bedrock2.Test
open FullLearnAnaTactics FullLearnAnaHelpers
open scoped FullArenaTactics FullLearnAnaTactics

/-! ## 1. Local `FullLearnAnaSpecs` Conversions & Unit-Learn Helper -/

private theorem s13_laOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem s13_canon_to_laOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem s13_laOtfsInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, s13_laOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s13_canon_to_laOtfsInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, s13_canon_to_laOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s13_laSparse_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullSparseInvW c F0 F_cur s) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s13_canon_to_laSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s13_sparse_with_iterating {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hs : FullSparseInvW c F0 F_cur s) (v : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with iterating := v } } := by
  have hscr : ({ s.scratch with iterating := v } : FullScratch).LengthsOk c :=
    { hs.1.scratch_ok with }
  exact ⟨⟨hs.1.core_ok, hscr⟩, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

private theorem s13_learn_unit_iter_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s_fin : FullState} {uip : BitVec 32}
    {R : Mem 64 → Prop} {m_f : Mem 64}
    (hEsub : ∀ a m Q X, step13EagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hext : M6HdrExtOk ext) (hfin_sparse : FullSparseInvW c F0 F_cur s_fin)
    (hcur_lt : s_fin.core.cur_level < s.core.cur_level)
    (hcv_eq : s_fin.core.cur_vars = s.core.cur_vars)
    (hfu_le : s_fin.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hws2_eq : s_fin.scratch.work_stk2 = s.scratch.work_stk2)
    (htl_eq : s_fin.core.tmp_len = 1) (htmp0 : s_fin.core.tmp[0]? = some uip)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars)
    (hm_f : (FullMem c s_fin ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_f)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _Jit => Blocks.cons
          (fun _ =>
            Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
              "full_eager_subsume" (Arg.var c.hdr, Arg.imm 4294967295, ())
              fun (_ : Tup Val []) => Expr.ret (rs := [i64]) (Arg.imm 1, ()))
          Blocks.nil)
        (fun Jit =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 520, ()) } fun pp0 =>
          Expr.load i64 (Arg.var pp0.1) fun ldp =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var ldp, Arg.imm 0, ()) } fun cp =>
          Expr.jnz (Arg.var cp.1)
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 1032, ()) } fun pi0 =>
            Expr.store (Arg.imm (t := i64) 1) (Arg.var pi0.1) (Expr.jump Jit.1 ()))
            (Expr.jump Jit.1 ()))) m_f := by
  let Rext : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hfin_sparse.1.core_ok.cur_vars_le
  c0_clean; c0_to_group
  refine wp_join_group (ts := []) (fun () m_it =>
      ∃ it_v : BitVec 64,
        let s_it : FullState := { s_fin with scratch := { s_fin.scratch with iterating := it_v } }
        FullSparseInvW c F0 F_cur s_it ∧ (FullMem c s_it ⋆ Rext) m_it) ?_ ?_
  · rintro _ ⟨⟩ m_it ⟨it_v, hit_sp, hm_it⟩
    let s_it : FullState := { s_fin with scratch := { s_fin.scratch with iterating := it_v } }
    have htmp_it_lt : ∀ k < s_it.core.tmp_len,
        (s_it.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
      have hk0 : k = 0 := by change k < s_fin.core.tmp_len at hk; omega
      subst hk0
      have hu0 : (s_it.core.tmp[0]?.getD 0#32) = uip := by
        change s_fin.core.tmp[0]?.getD 0#32 = uip; rw [htmp0, Option.getD_some]
      rw [hu0]; omega
    c0_clean; c0_call hEsub
    refine ⟨c, F0, F_cur, s_it, Rext, rfl, hit_sp, htmp_it_lt, fun hlt => absurd hlt (by decide),
      hm_it, ?_⟩
    intro ar' ag' _nr' sc'' m_sub _ hsub_sp hws2' hm_sub
    c0_steps
    exact hQ 1#64 ext _ m_sub hext hsub_sp.1 (Or.inr (Or.inl rfl)) hcv_eq hfu_le
      (hws2'.trans hws2_eq) (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨hsub_sp, hcur_lt⟩) (fullM6HdrMem_unfocus_full hm_sub)
  · intro Jit hJit
    c0_clean; c0_split
    · c0_steps
      exact hJit () _ ⟨1#64, s13_sparse_with_iterating hfin_sparse 1#64, by assumption⟩
    · c0_steps
      exact hJit () m_f ⟨s_fin.scratch.iterating,
        by simpa only [] using s13_sparse_with_iterating hfin_sparse s_fin.scratch.iterating,
        hm_f⟩

private theorem s13_learn_unit_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState} {uip : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, step13EagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hext : M6HdrExtOk ext) (hs_c : FullOtfsInvW c F0 F_cur s)
    (hcur_pos : 0 < s.core.cur_level) (htl_is1 : s.core.tmp_len = 1)
    (huip_in : 0 < s.core.tmp.length) (huip_0 : s.core.tmp[0]? = some uip)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)))
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    let _Rext : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) (rs := [i64])
        "full_det_new_level" (Arg.var c.hdr, Arg.imm 0, ()) fun nlvl_res =>
      Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
        "full_backtrack_ac_fid" (Arg.var c.hdr, Arg.var nlvl_res.1, ()) fun (_ : Tup Val []) =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var uip, ()) } fun p0 =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.pVals, Arg.var p0.1, ()) }
        fun p1 =>
      Expr.load i8 (Arg.var p1.1) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p2 =>
      Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun p3 =>
      Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p2.1, ()) } fun p4 =>
      Expr.let_
        { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
          args := (Arg.var p3.1, Arg.var p4.1, ()) } fun p5 =>
      Expr.jnz (Arg.var p5.1) (Expr.ret (Arg.imm 0, ()))
        (Expr.call (as := [i64, i32, i32, i32]) (bs := []) (rs := [i64])
          "full_assign_lvl" (Arg.var c.hdr, Arg.var uip, Arg.imm 4294967295, Arg.imm 0, ())
          fun (_ : Tup Val []) =>
        Expr.group (sig := [[]])
          (fun _Jit => Blocks.cons
            (fun _ =>
              Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
                "full_eager_subsume" (Arg.var c.hdr, Arg.imm 4294967295, ())
                fun (_ : Tup Val []) => Expr.ret (rs := [i64]) (Arg.imm 1, ()))
            Blocks.nil)
          fun Jit =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 520, ()) } fun pp0 =>
          Expr.load i64 (Arg.var pp0.1) fun ldp =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var ldp, Arg.imm 0, ()) } fun cp =>
          Expr.jnz (Arg.var cp.1)
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 1032, ()) } fun pi0 =>
            Expr.store (Arg.imm (t := i64) 1) (Arg.var pi0.1) (Expr.jump Jit.1 ()))
            (Expr.jump Jit.1 ()))) m := by
  intro Rext
  have hs := s13_canon_to_laOtfsInv hs_c
  have hcl := hs.1.core_ok
  have hw := hs.2.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl.cur_vars_le
  have hte_le := hcl.trail_end_le
  have hcur_le := hw.cur_level_le
  have hent_unit : (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat]) := by
    rwa [htl_is1, s13_tmp_take1_eq huip_in huip_0] at hent
  c0_to_group; c0_call hDnl
  refine ⟨c, s, Rext, rfl, hs.1, by omega, hm, fun nlvl_u _ hnlvl_fn => ?_⟩
  obtain ⟨_, hnlvl_lt⟩ := hnlvl_fn hcur_pos (by simp; exact hcur_pos)
  c0_to_group; c0_call hBt
  refine ⟨c, s, Rext, rfl, hs.1, by omega, fun _ => by omega, hw.trail_lits_lt, hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt s_bt
    hbt_len _ _ hbt_cl hbt_pres _ _ _ _ hbt_otfs hm_bt
  have hcl_nl : cl' = nlvl_u.toNat := by rw [hbt_cl]; exact Nat.min_eq_right (Nat.le_of_lt hnlvl_lt)
  have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hs_c.2.1 hnlvl_lt
  have hbt_sparse := s13_laSparse_to_canon
    (fullBacktrack_preserves_fullSparseW hs hbt_len hbt_w rfl rfl rfl rfl rfl hbt_pres.1)
  have huip_vlen : uip.toNat < vals'.length := by
    have hvl := hbt_len.core_ok.vals_len; dsimp only [s_bt] at hvl; omega
  c0_clean; c0_split
  · c0_clean; c0_steps
    exact hQ 0#64 ext s_bt m_bt hext hbt_len (Or.inl rfl) rfl (Nat.le_refl _) hbt_pres.2.2.1
      (fun h => by cases h) (fun _ => hbt_sparse) (fun h => by cases h)
      (fullM6HdrMem_unfocus_full hm_bt)
  · have huip_z : vals'[uip.toNat]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
      exact (i8_sext32_eq0 _).mp (by assumption)
    have hbt_te_lt : te' < c.max_vars := by
      have := hbt_w.trail_end_lt_of_unassigned huip_lt huip_z; dsimp only [s_bt] at this; omega
    c0_to_group; c0_call hAsgn
    refine ⟨c, s_bt, Rext, rfl, hbt_len, hm_bt, ?_⟩
    rw [ite_eq_right (fun h => by
      dsimp only [s_bt] at h; simp only [huip_z, ne_eq, not_true_eq_false, or_false] at h
      omega)]
    intro v rsn_let unfl_let flags' unass'' phases' m_f hfll hph s_f0 hm_f
    have hrsn_let : rsn_let = 0xFFFFFFFF#32 := ite_eq_left rfl
    have hunfl_let : unfl_let = s_bt.core.unflushed + 1#64 := ite_eq_left rfl
    let s_fin : FullState :=
      { s_bt with
        core :=
          { s_bt.core with
            vals := (vals'.set uip.toNat 1#8).set (uip.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := lvl'.set (uip.toNat / 2) 0#32
            rsns := rsns'.set (uip.toNat / 2) 0xFFFFFFFF#32
            trl := trl'.set te' uip
            trail_pos := tp'.set (uip.toNat / 2) (BitVec.ofNat 32 te')
            trail_end := te' + 1, unassigned := unass''
            unflushed := s_bt.core.unflushed + 1#64 }
        scratch := { sc' with phases := phases' } }
    have hsc_f : s_fin.scratch.LengthsOk c := { hbt_len.scratch_ok with phases_len := hph }
    have ⟨hfin_len, hfin_w⟩ := chronoAssign_preserves_fullWitness hbt_w hbt_len hsc_f
      (rsn := 0xFFFFFFFF#32) (unassigned' := unass'') (unflushed' := s_bt.core.unflushed + 1#64)
      hfll huip_lt huip_z (Nat.zero_le _) (fun h => by omega) (fun _ => hent_unit)
      (fun h _ => by omega) (fun h _ _ => by omega)
    have hfin_sparse : FullSparseInvW c F0 F_cur s_fin :=
      ⟨hfin_len, hfin_w, hbt_sparse.2.2.1, hbt_sparse.2.2.2.1, hbt_sparse.2.2.2.2.1,
        hbt_sparse.2.2.2.2.2⟩
    have hm_f' : (FullMem c s_fin ⋆ Rext) m_f := by
      simpa only [s_fin, s_f0, s_bt, v, hrsn_let, hunfl_let,
        show (0 : BitVec 32) = 0#32 from rfl] using hm_f
    exact s13_learn_unit_iter_wp (s := s) (s_fin := s_fin) hEsub hext hfin_sparse
      (by dsimp only [s_fin, s_bt]; rw [hcl_nl]; exact hnlvl_lt) rfl (Nat.le_refl _)
      (by dsimp only [s_fin, s_bt]; exact hbt_pres.2.2.1) htl_is1
      (by dsimp only [s_fin, s_bt]; exact huip_0) huip_lt hm_f' hQ

/-! ## 2. Pre-Add Headroom & 3-Step Retry Helpers -/

private theorem s13_learn_pre_gc_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s_bt : FullState} {uip : BitVec 32}
    {nlvl : BitVec 64} {tmp_sw : List (BitVec 32)} {vals_bt : List (BitVec 8)}
    {lvl_bt trl_bt : List (BitVec 32)} {te_bt : Nat} {R : Mem 64 → Prop} {m_bt : Mem 64}
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hbt_pre : S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_bt)
    (_huip_in : 0 < s.core.tmp.length) (_huip_0 : s.core.tmp[0]? = some uip)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars)
    (hnlvl_pos : 0 < nlvl.toNat) (hnlvl_lt : nlvl.toNat < s.core.cur_level)
    (hm_bt : (FullM6HdrMem c ext s_bt ⋆ R) m_bt)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    {k : Expr Val Cont [i64]}
    (hk : ∀ (ext_gc : List (BitVec 64)) (s_gc : FullState) (m_gc : Mem 64),
      M6HdrExtOk ext_gc →
      S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_gc →
      (FullM6HdrMem c ext_gc s_gc ⋆ R) m_gc → wp Γ Q X k m_gc) :
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _Jgc => Blocks.cons (fun _ => k) Blocks.nil)
        (fun Jgc =>
          Expr.group (sig := [[]])
            (fun _Jin => Blocks.cons
              (fun _ =>
                Expr.group (sig := [[]])
                  (fun _Jdef => Blocks.cons
                    (fun _ =>
                      Expr.group (sig := [[]])
                        (fun _J3 => Blocks.cons (fun _ => Expr.jump Jgc.1 ()) Blocks.nil)
                        (fun J3 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p0 =>
                          Expr.load i64 (Arg.var p0.1) fun alen =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 192, ()) } fun p1 =>
                          Expr.load i64 (Arg.var p1.1) fun tlen =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var alen, Arg.var tlen, ()) } fun p2 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var p2.1, Arg.imm 8, ()) } fun p3 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 32, ()) } fun p4 =>
                          Expr.load i64 (Arg.var p4.1) fun acap =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                              args := (Arg.var p3.1, Arg.var acap, ()) } fun p5 =>
                          Expr.jnz (Arg.var p5.1)
                            (Expr.call (as := [i64, .bool]) (bs := [i64]) (rs := [i64])
                              "full_reduce_m6" (Arg.var c.hdr, Arg.imm true, ()) fun rr =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                args := (Arg.var rr.1, Arg.imm 20, ()) } fun c20 =>
                            Expr.jnz (Arg.var c20.1) (Expr.ret (Arg.imm 20, ()))
                              (Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                  args := (Arg.var rr.1, Arg.imm 1, ()) } fun cn1 =>
                              Expr.jnz (Arg.var cn1.1) (Expr.ret (Arg.imm 0, ()))
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.hdr, Arg.imm 160, ()) } fun pcl =>
                                Expr.load i64 (Arg.var pcl.1) fun cl =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                    args := (Arg.var cl, Arg.var nlvl, ()) } fun cne =>
                                Expr.jnz (Arg.var cne.1) (Expr.ret (Arg.imm 1, ()))
                                  (Expr.let_
                                    { sig := [i32], code := OpCode.zext 32 64,
                                      args := (Arg.var uip, ()) } fun pu0 =>
                                  Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var c.pVals, Arg.var pu0.1, ()) } fun pu1 =>
                                  Expr.load i8 (Arg.var pu1.1) fun ld =>
                                  Expr.let_
                                    { sig := [i32], code := OpCode.trunc 32 8,
                                      args := (Arg.imm 0, ()) } fun pz =>
                                  Expr.let_
                                    { sig := [i8], code := OpCode.sext 8 32,
                                      args := (Arg.var ld, ()) } fun ps0 =>
                                  Expr.let_
                                    { sig := [i8], code := OpCode.sext 8 32,
                                      args := (Arg.var pz.1, ()) } fun ps1 =>
                                  Expr.let_
                                    { sig := [i32, i32],
                                      code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                                      args := (Arg.var ps0.1, Arg.var ps1.1, ()) } fun pu_ne =>
                                  Expr.jnz (Arg.var pu_ne.1) (Expr.ret (Arg.imm 1, ()))
                                    (Expr.jump J3.1 ())))))
                            (Expr.jump J3.1 ())))
                    Blocks.nil)
                  (fun Jdef =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var c.hdr, Arg.imm 464, ()) } fun pw =>
                    Expr.load i64 (Arg.var pw.1) fun wu =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                        args := (Arg.var wu, Arg.imm 0, ()) } fun cwu =>
                    Expr.jnz (Arg.var cwu.1)
                      (Expr.call (as := [i64]) (bs := []) (rs := [i64])
                        "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
                        Expr.jump Jdef.1 ())
                      (Expr.jump Jdef.1 ())))
              Blocks.nil)
            (fun J_in =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.hdr, Arg.imm 48, ()) } fun pa =>
              Expr.load i64 (Arg.var pa.1) fun alen =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.hdr, Arg.imm 192, ()) } fun pt =>
              Expr.load i64 (Arg.var pt.1) fun tlen =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var alen, Arg.var tlen, ()) } fun p1 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p1.1, Arg.imm 8, ()) } fun p2 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.hdr, Arg.imm 32, ()) } fun pc =>
              Expr.load i64 (Arg.var pc.1) fun acap =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                  args := (Arg.var p2.1, Arg.var acap, ()) } fun cmp1 =>
              Expr.jnz (Arg.var cmp1.1) (Expr.jump J_in.1 ())
                (Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 40, ()) } fun pwc =>
                Expr.load i64 (Arg.var pwc.1) fun wcap =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 56, ()) } fun pwl =>
                Expr.load i64 (Arg.var pwl.1) fun wlen =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.sub i64,
                    args := (Arg.var wcap, Arg.var wlen, ()) } fun pd =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                    args := (Arg.var pd.1, Arg.imm 32, ()) } fun cmp2 =>
                Expr.jnz (Arg.var cmp2.1) (Expr.jump J_in.1 ()) (Expr.jump Jgc.1 ()))))) m_bt := by
  have ⟨hbt_sp, hcl_bt, hbt_cv, hbt_fu, hbt_tmp, hbt_tl, hbt_vals, hbt_lvl, hbt_trl, hbt_te,
    hbt_ws2⟩ := hbt_pre
  have hbt_len := hbt_sp.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  let Rext : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  have hm_btf := fullM6HdrMem_focus_full hm_bt
  change (FullMem c s_bt ⋆ Rext) m_bt at hm_btf
  c0_to_group
  refine wp_join_group (ts := []) (fun () m_gc =>
      ∃ (ext_gc : List (BitVec 64)) (s_gc : FullState),
        M6HdrExtOk ext_gc ∧
        S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_gc ∧
        (FullM6HdrMem c ext_gc s_gc ⋆ R) m_gc) ?_ ?_
  · rintro _ ⟨⟩ m_gc ⟨ext_gc, s_gc, hext_gc, hgc_pre, hm_gc⟩
    exact hk ext_gc s_gc m_gc hext_gc hgc_pre hm_gc
  · intro Jgc hJgc
    c0_to_group
    refine wp_join_group (ts := []) (fun () m_in => m_in = m_bt) ?_ ?_
    · rintro _ ⟨⟩ m_in rfl
      c0_to_group
      refine wp_join_group (ts := []) (fun () m_d => ∃ wvec_d wstk_d wlen_d wsort_d,
          let s_d : FullState :=
            { s_bt with
              core := { s_bt.core with
                wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
              scratch := { s_bt.scratch with wsort := wsort_d } }
          FullSparseInvW c F0 F_cur s_d ∧ (FullMem c s_d ⋆ Rext) m_d) ?_ ?_
      · rintro _ ⟨⟩ m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
        let s_d : FullState :=
          { s_bt with
            core := { s_bt.core with
              wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
            scratch := { s_bt.scratch with wsort := wsort_d } }
        have hd_cl : s_d.core.cur_level = nlvl.toNat := hcl_bt
        c0_to_group
        refine wp_join_group (ts := []) (fun () m_3 =>
            ∃ (ext_3 : List (BitVec 64)) (s_3 : FullState),
              M6HdrExtOk ext_3 ∧
              S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_3 ∧
              (FullM6HdrMem c ext_3 s_3 ⋆ R) m_3) ?_ ?_
        · rintro _ ⟨⟩ m_3 ⟨ext_3, s_3, hext_3, h3_pre, hm_3⟩
          c0_steps; exact hJgc () m_3 ⟨ext_3, s_3, hext_3, h3_pre, hm_3⟩
        · intro J3 hJ3; c0_split
          · c0_to_group; c0_call hRedM6
            refine m6ReduceSpec_of (FullM6HdrInvW.mk_inv hcfg hext hd_sp)
              (fullM6HdrMem_unfocus_full hm_d) ?_
            intro rr ext_r s_r m_r hr_inv hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
              hr_20 _ hr_pos hm_r
            have hr_sp : FullSparseInvW c F0 F_cur s_r := hr_inv.sparseW
            have hext_r : M6HdrExtOk ext_r := hr_inv.extOk
            dsimp only [s_d] at hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2 hr_pos
            have hr_cv' : s_r.core.cur_vars = s.core.cur_vars := hr_cv.trans hbt_cv
            have hr_fu' : s_r.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hr_fu hbt_fu
            have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 := hr_ws2.trans hbt_ws2
            have hr_tmp' : s_r.core.tmp = tmp_sw := hr_tmp.trans hbt_tmp
            have hr_tl' : s_r.core.tmp_len = s.core.tmp_len := hr_tl.trans hbt_tl
            have _hm_rf := fullM6HdrMem_focus_full hm_r
            c0_hsplit
            · c0_hsteps
              exact hQ 20#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv' hr_fu'
                hr_ws2' (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, by omega⟩)
                (fun h => by cases h) (fun h => by cases h) hm_r
            · c0_hsplit
              · c0_hsteps
                exact hQ 0#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inl rfl) hr_cv' hr_fu' hr_ws2'
                  (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
              · have hrr1 : rr = 1#64 := by
                  rcases hr_dom with rfl | rfl | rfl
                  · exfalso; simp [bv_c0] at hc
                  · rfl
                  · exfalso; simp [bv_c0] at hc
                c0_hsplit
                · c0_hsteps
                  exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv'
                    hr_fu' hr_ws2' (fun h => by cases h) (fun h => by cases h)
                    (fun _ => ⟨hr_sp, by omega⟩) hm_r
                · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                    have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by
                      simpa [bv_c0] using hc
                    have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                      have := hr_sp.1.core_ok.cur_vars_le
                      have := hr_sp.2.1.cur_level_le
                      have := hr_sp.1.core_ok.trail_end_le; omega
                    have := congrArg BitVec.toNat hbv
                    rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                  have huip_r_lt : uip.toNat < s_r.core.vals.length := by
                    have := hr_sp.1.core_ok.cur_vars_le
                    rw [hr_sp.1.core_ok.vals_len]; omega
                  c0_hsplit
                  · c0_hsteps
                    exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv'
                      hr_fu' hr_ws2' (fun h => by cases h) (fun h => by cases h)
                      (fun _ => ⟨hr_sp, by omega⟩) hm_r
                  · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                      hr_pos hrr1 (hcl_eq ▸ hnlvl_pos)
                    c0_hsteps
                    exact hJ3 () m_r ⟨ext_r, s_r, hext_r,
                      ⟨hr_sp, hcl_eq, hr_cv', hr_fu', hr_tmp', hr_tl', hr_vals.trans hbt_vals,
                        hr_lvl.trans hbt_lvl, hr_trl.trans hbt_trl, hr_te.trans hbt_te, hr_ws2'⟩,
                      hm_r⟩
          · c0_steps
            exact hJ3 () m_d ⟨ext, s_d, hext,
              ⟨hd_sp, hd_cl, hbt_cv, hbt_fu, hbt_tmp, hbt_tl, hbt_vals, hbt_lvl, hbt_trl,
                hbt_te, hbt_ws2⟩,
              fullM6HdrMem_unfocus_full hm_d⟩
      · intro Jdef hJdef; c0_split
        · have hbt_lay : WatchStackLayout s_bt.core := by
            have hm_w := hbt_sp.2.1.watches
            unfold ModeWatchesInv at hm_w
            rw [ite_eq_left hbt_sp.2.2.2.2.2] at hm_w
            exact hm_w.layout
          c0_call hDefrag
          refine ⟨c, s_bt, Rext, rfl, hbt_len, hbt_lay, hm_btf, ?_⟩
          intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
          let s_d : FullState :=
            { s_bt with
              core := { s_bt.core with
                wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
              scratch := { s_bt.scratch with wsort := wsort_d } }
          have hd_sp := s13_laSparse_to_canon
            (fullWstackDefrag_preserves_fullSparseW (s13_canon_to_laSparse hbt_sp)
              hd_len hd_lay hd_pres)
          c0_steps
          exact hJdef () m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
        · have hwuz : s_bt.core.wusable = 0#64 := by
            apply BitVec.eq_of_toNat_eq; bv_omega
          have hs_eq :
              ({ s_bt with core := { s_bt.core with wusable := 0#64 } } : FullState) =
              s_bt := by
            cases s_bt with | mk kc sc => cases kc; dsimp only at hwuz ⊢; simp [hwuz]
          c0_steps
          refine hJdef () m_in ⟨s_bt.core.wvec, s_bt.core.wstk, s_bt.core.wlen, s_bt.scratch.wsort,
            ?_, ?_⟩
          · simpa only [hs_eq] using hbt_sp
          · simpa only [hs_eq] using hm_btf
    · intro J_in hJ_in; c0_split
      · c0_steps; exact hJ_in () m_bt rfl
      · c0_split
        · c0_steps; exact hJ_in () m_bt rfl
        · c0_steps
          exact hJgc () m_bt ⟨ext, s_bt, hext, hbt_pre, hm_bt⟩

private theorem s13_learn_retry_step_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext_lp : List (BitVec 64)} {s s_lp : FullState}
    {uip : BitVec 32} {nlvl step : BitVec 64} {tmp_sw : List (BitVec 32)}
    {vals_bt : List (BitVec 8)} {lvl_bt trl_bt : List (BitVec 32)} {te_bt : Nat}
    {R : Mem 64 → Prop} {mL : Mem 64}
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ h m Q X, Full.fullReduceSpec (h, true, ()) m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] (h, ()) m Q X)
    (hcfg : FullM6HdrCfgOk c) (hext_lp : M6HdrExtOk ext_lp)
    (hlp_pre : S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_lp)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars)
    (hnlvl_pos : 0 < nlvl.toNat) (hnlvl_lt : nlvl.toNat < s.core.cur_level)
    (hmL : (FullM6HdrMem c ext_lp s_lp ⋆ R) mL)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (J1 : Cont [])
    (hJ1 : ∀ m_pre,
      (∃ (ext_pre : List (BitVec 64)) (s_pre : FullState),
        M6HdrExtOk ext_pre ∧
        S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_pre ∧
        (FullM6HdrMem c ext_pre s_pre ⋆ R) m_pre) →
      J1 () m_pre) :
    wp Γ Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var step, Arg.imm 0, ()) } fun cs0 =>
      Expr.jnz (Arg.var cs0.1)
        (Expr.group (sig := [[]])
          (fun _Jd => Blocks.cons (fun _ => Expr.jump J1 ()) Blocks.nil)
          (fun Jd =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 464, ()) } fun pw =>
            Expr.load i64 (Arg.var pw.1) fun wu =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                args := (Arg.var wu, Arg.imm 0, ()) } fun cwu =>
            Expr.jnz (Arg.var cwu.1)
              (Expr.call (as := [i64]) (bs := []) (rs := [i64])
                "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
                Expr.jump Jd.1 ())
              (Expr.jump Jd.1 ())))
        (Expr.group (sig := [[i64]])
          (fun _Jr => Blocks.cons
            (fun gr =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var gr.1, Arg.imm 20, ()) } fun c20 =>
              Expr.jnz (Arg.var c20.1) (Expr.ret (Arg.imm 20, ()))
                (Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                    args := (Arg.var gr.1, Arg.imm 1, ()) } fun cn1 =>
                Expr.jnz (Arg.var cn1.1) (Expr.ret (Arg.imm 0, ()))
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 160, ()) } fun pcl =>
                  Expr.load i64 (Arg.var pcl.1) fun cl =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                      args := (Arg.var cl, Arg.var nlvl, ()) } fun cne =>
                  Expr.jnz (Arg.var cne.1) (Expr.ret (Arg.imm 1, ()))
                    (Expr.let_
                      { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var uip, ()) } fun pu0 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var c.pVals, Arg.var pu0.1, ()) } fun pu1 =>
                    Expr.load i8 (Arg.var pu1.1) fun ld =>
                    Expr.let_
                      { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun pz =>
                    Expr.let_
                      { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun ps0 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.sext 8 32,
                        args := (Arg.var pz.1, ()) } fun ps1 =>
                    Expr.let_
                      { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                        args := (Arg.var ps0.1, Arg.var ps1.1, ()) } fun pune =>
                    Expr.jnz (Arg.var pune.1) (Expr.ret (Arg.imm 1, ())) (Expr.jump J1 ())))))
            Blocks.nil)
          (fun Jr =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                args := (Arg.var step, Arg.imm 1, ()) } fun cs1 =>
            Expr.jnz (Arg.var cs1.1)
              (Expr.call (as := [i64, .bool]) (bs := [i64]) (rs := [i64])
                "full_reduce_m6" (Arg.var c.hdr, Arg.imm true, ()) fun gr =>
                Expr.jump Jr.1 (Arg.var gr.1, ()))
              (Expr.call (as := [i64]) (bs := [i64]) (rs := [i64])
                "full_reduce_purge_c0" (Arg.var c.hdr, ()) fun gr =>
                Expr.jump Jr.1 (Arg.var gr.1, ()))))) mL := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hmLf := fullM6HdrMem_focus_full hmL
  c0_split
  · c0_to_group
    refine wp_join_group (ts := []) (fun () m_d => ∃ s_d : FullState,
        S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_d ∧
        (FullM6HdrMem c ext_lp s_d ⋆ R) m_d) ?_ ?_
    · rintro _ ⟨⟩ m_d ⟨s_d, hd_pre, hm_d⟩
      c0_steps; exact hJ1 m_d ⟨ext_lp, s_d, hext_lp, hd_pre, hm_d⟩
    · intro Jd hJd
      have ⟨hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl, hlp_trl, hlp_te,
        hlp_ws2⟩ := hlp_pre
      c0_split
      · have hlp_lay : WatchStackLayout s_lp.core := by
          have hm_w := hlp_sp.2.1.watches
          unfold ModeWatchesInv at hm_w
          rw [ite_eq_left hlp_sp.2.2.2.2.2] at hm_w
          exact hm_w.layout
        c0_call hDefrag
        refine ⟨c, s_lp, m6ExtMem (m6ExtAddr c.hdr) ext_lp ⋆ R, rfl, hlp_sp.1, hlp_lay, hmLf, ?_⟩
        intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
        let s_d : FullState :=
          { s_lp with
            core := { s_lp.core with
              wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
            scratch := { s_lp.scratch with wsort := wsort_d } }
        have hd_sp := s13_laSparse_to_canon
          (fullWstackDefrag_preserves_fullSparseW (s13_canon_to_laSparse hlp_sp)
            hd_len hd_lay hd_pres)
        c0_steps
        exact hJd () m_d ⟨s_d, ⟨hd_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals,
          hlp_lvl, hlp_trl, hlp_te, hlp_ws2⟩, fullM6HdrMem_unfocus_full hm_d⟩
      · have hwuz : s_lp.core.wusable = 0#64 := by apply BitVec.eq_of_toNat_eq; bv_omega
        c0_steps
        exact hJd () mL ⟨s_lp, hlp_pre, by simpa only [hwuz] using hmL⟩
  · c0_to_group
    refine wp_join_group (ts := [i64]) (fun (gr, ()) m_r =>
        ∃ (ext_r : List (BitVec 64)) (s_r : FullState),
          M6HdrExtOk ext_r ∧ FullSparseInvW c F0 F_cur s_r ∧ (gr = 0#64 ∨ gr = 1#64 ∨ gr = 20#64) ∧
          s_r.core.cur_level ≤ s_lp.core.cur_level ∧
          s_r.core.fuel.toNat ≤ s_lp.core.fuel.toNat ∧ s_r.core.cur_vars = s_lp.core.cur_vars ∧
          s_r.core.tmp = s_lp.core.tmp ∧ s_r.core.tmp_len = s_lp.core.tmp_len ∧
          s_r.scratch.work_stk2 = s_lp.scratch.work_stk2 ∧ (gr = 20#64 → F0.Unsat) ∧
          (gr = 1#64 → 0 < s_r.core.cur_level →
            s_r.core.cur_level = s_lp.core.cur_level ∧ s_r.core.vals = s_lp.core.vals ∧
            s_r.core.lvl = s_lp.core.lvl ∧ s_r.core.trl = s_lp.core.trl ∧
            s_r.core.trail_pos = s_lp.core.trail_pos ∧ s_r.core.trail_end = s_lp.core.trail_end) ∧
          (FullM6HdrMem c ext_r s_r ⋆ R) m_r) ?_ ?_
    · rintro _ ⟨gr, ⟨⟩⟩ m_r ⟨ext_r, s_r, hext_r, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv,
        hr_tmp, hr_tl, hr_ws2, hr_20, hr_pos, hm_r⟩
      have ⟨_hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl, hlp_trl, hlp_te,
        hlp_ws2⟩ := hlp_pre
      have hr_cv' : s_r.core.cur_vars = s.core.cur_vars := hr_cv.trans hlp_cv
      have hr_fu' : s_r.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hr_fu hlp_fu
      have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 := hr_ws2.trans hlp_ws2
      have hcl_lt_s : s_r.core.cur_level < s.core.cur_level := by
        have := hr_cl; have := hlp_cl; omega
      have _hm_rf := fullM6HdrMem_focus_full hm_r
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv' hr_fu' hr_ws2'
          (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, hcl_lt_s⟩)
          (fun h => by cases h) (fun h => by cases h) hm_r
      · c0_hsplit
        · c0_hsteps
          exact hQ 0#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inl rfl) hr_cv' hr_fu' hr_ws2'
            (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
        · have hgr1 : gr = 1#64 := by
            rcases hr_dom with rfl | rfl | rfl
            · exfalso; simp [bv_c0] at hc
            · rfl
            · exfalso; simp [bv_c0] at hc
          c0_hsplit
          · c0_hsteps
            exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv' hr_fu'
              hr_ws2' (fun h => by cases h) (fun h => by cases h) (fun _ => ⟨hr_sp, hcl_lt_s⟩)
              hm_r
          · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
              have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by simpa [bv_c0] using hc
              have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                have := hr_sp.1.core_ok.cur_vars_le
                have := hr_sp.2.1.cur_level_le
                have := hr_sp.1.core_ok.trail_end_le; omega
              have := congrArg BitVec.toNat hbv
              rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
            have huip_r_lt : uip.toNat < s_r.core.vals.length := by
              have hcv_r : s_r.core.cur_vars ≤ c.max_vars := hr_sp.1.core_ok.cur_vars_le
              rw [hr_cv'] at hcv_r
              rw [hr_sp.1.core_ok.vals_len]; omega
            c0_hsplit
            · c0_hsteps
              exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv' hr_fu'
                hr_ws2' (fun h => by cases h) (fun h => by cases h)
                (fun _ => ⟨hr_sp, hcl_lt_s⟩) hm_r
            · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                hr_pos hgr1 (hcl_eq ▸ hnlvl_pos)
              c0_hsteps
              exact hJ1 m_r ⟨ext_r, s_r, hext_r, ⟨hr_sp, hcl_eq, hr_cv', hr_fu',
                hr_tmp.trans hlp_tmp, hr_tl.trans hlp_tl, hr_vals.trans hlp_vals,
                hr_lvl.trans hlp_lvl, hr_trl.trans hlp_trl, hr_te.trans hlp_te, hr_ws2'⟩, hm_r⟩
    · intro Jr hJr
      c0_split
      · c0_call hRedM6
        refine m6ReduceSpec_of (FullM6HdrInvW.mk_inv hcfg hext_lp hlp_pre.1) hmL ?_
        intro rr ext_r s_r m_r hr_inv hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
          hr_20 _ hr_pos hm_r
        c0_steps
        exact hJr (rr, ()) m_r ⟨ext_r, s_r, hr_inv.extOk, hr_inv.sparseW, hr_dom, hr_cl, hr_fu,
          hr_cv, hr_tmp, hr_tl, hr_ws2, hr_20, hr_pos, hm_r⟩
      · c0_call hRedPurge
        refine ⟨c, F0, F_cur, s_lp, m6ExtMem (m6ExtAddr c.hdr) ext_lp ⋆ R,
          rfl, hlp_pre.1, hmLf, ?_⟩
        intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
          hr_20 _ hr_pos hm_r
        c0_steps
        exact hJr (rr, ()) m_r ⟨ext_lp, s_r, hext_lp, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv, hr_tmp,
          hr_tl, hr_ws2, hr_20, hr_pos, fullM6HdrMem_unfocus_full hm_r⟩

private theorem s13_learn_post_ac_m6_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext_ex : List (BitVec 64)} {s s_ex : FullState}
    {R : Mem 64 → Prop} {m_ex : Mem 64} {uip_lit wm : BitVec 32} {new_ref64 nlvl : BitVec 64}
    {max_lvl : Nat} {tmp_sw : List (BitVec 32)} {vals_bt : List (BitVec 8)}
    {lvl_bt trl_bt : List (BitVec 32)} {te_bt : Nat}
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, step13EagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hext_ex : M6HdrExtOk ext_ex)
    (hex_pre : S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_ex)
    (hex_nr : S13NrSpec F_cur s uip_lit wm tmp_sw s_ex new_ref64)
    (hml_pos : 0 < max_lvl) (hnlvl_ge : max_lvl ≤ nlvl.toNat)
    (hnlvl_lt : nlvl.toNat < s.core.cur_level)
    (hsw_1 : tmp_sw[1]? = some wm)
    (htl_ge2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (huip_lt : uip_lit.toNat < 2 * s.core.cur_vars) (hwm_lt : wm.toNat < 2 * s.core.cur_vars)
    (htmp_sw_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hwm_on_bt : ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
      (lvl_bt[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hlow_bt : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
      q = uip_lit.toNat ∨ ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        (lvl_bt[q / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hm_ex : (FullM6HdrMem c ext_ex s_ex ⋆ R) m_ex)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (s13PostAcExpr c uip_lit new_ref64 max_lvl) m_ex := by
  rcases hex_pre with ⟨hex_sp, hex_cl, hex_cv, hex_fu, hex_tmp, hex_tl,
    hex_vals, hex_lvl, hex_trl, hex_te, hex_ws2⟩
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have _hm_exf := fullM6HdrMem_focus_full hm_ex
  exact s13_learn_clause_post_ac_wp (c := c) (F0 := F0) (F_cur := F_cur) (s := s) (s_ac := s_ex)
    (R := m6ExtMem (m6ExtAddr c.hdr) ext_ex ⋆ R) (m_ac := m_ex)
    (uip_lit := uip_lit) (wm := wm) (new_ref64 := new_ref64) (max_lvl := max_lvl)
    (tmp_sw := tmp_sw) hAsgn hEsub
    (fun r s' m' a1 a2 a3 a4 a5 a6 a7 a8 hm' =>
      hQ r ext_ex s' m' hext_ex a1 a2 a3 a4 a5 a6 a7 a8 (fullM6HdrMem_unfocus_full hm'))
    hex_sp (by rw [hex_cl]; exact hnlvl_lt) hml_pos (by rw [hex_cl]; exact hnlvl_ge)
    (by
      have := hex_sp.1.core_ok.cur_vars_le
      have := hex_sp.2.1.cur_level_le
      have := hex_sp.1.core_ok.trail_end_le
      omega)
    hex_cv hex_fu hex_ws2 hex_tmp hex_tl hsw_1 htl_ge2 htl_cv huip_lt hwm_lt htmp_sw_lt
    (by rw [hex_trl, hex_lvl, hex_te]; exact hwm_on_bt)
    (by rw [hex_trl, hex_lvl, hex_te]; exact hlow_bt)
    hex_nr _hm_exf

/-! ## 3. Main Theorem: `full_learn_clause_m6_step13_wp` -/

/-- Step-13 `full_learn_clause_m6` (unit `full_det_new_level`/`iterating`/`full_eager_subsume`,
no `tlen > 2` reverse phase, binary `jumpreasons`, pre-add GC + 3-step retry) satisfies
`step13LearnClauseM6Spec` parametrically in `Γ` and `X`. -/
theorem full_learn_clause_m6_step13_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, step13AddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, step13EagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ args m Q X, step13LearnClauseM6Spec args m Q X →
      Func.wp Γ fidStep13S2LearnClauseM6Fn.body args m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hs_c, hcur_pos, htl1,
    htl_cv, htmp_nd, htmp_vals, htmp_lvls, hent, hm0, hQ⟩
  have hs := s13_canon_to_laOtfsInv hs_c
  have hcl := hs.1.core_ok
  have hw := hs.2.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcur_le := hw.cur_level_le
  have hte_le := hcl.trail_end_le
  have hcv_le := hcl.cur_vars_le
  have htmp_len_arr := hcl.tmp_len_arr
  have huip_in : 0 < s.core.tmp.length := by omega
  let uip := s.core.tmp[0]'huip_in
  have huip_0 : s.core.tmp[0]? = some uip := List.getElem?_eq_getElem huip_in
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    have := (htmp_vals 0 htl1).1; rwa [huip_0, Option.getD_some] at this
  unfold Func.wp fidStep13S2LearnClauseM6Fn full_learn_clause_m6_body
  dsimp only
  have hm := fullM6HdrMem_focus_full hm0
  let Rext : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  change (FullMem c s ⋆ Rext) m at hm
  c0_clean; c0_split
  · have htl_is1 : s.core.tmp_len = 1 := by bv_omega
    exact s13_learn_unit_wp hDnl hBt hAsgn hEsub hext hs_c hcur_pos htl_is1 huip_in huip_0
      huip_lt hent hm hQ
  · have htl_ge2 : 2 ≤ s.core.tmp_len := by
      have hne : s.core.tmp_len ≠ 1 := by
        intro h1; have heq : BitVec.ofNat 64 s.core.tmp_len = 1#64 := by rw [h1]
        contradiction
      omega
    have htl_lt : s.core.tmp_len < 2 ^ 64 := by omega
    have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := bv64_ofNat_toNat htl_lt
    c0_clean; c0_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) m2 => ∃ t2 : List (BitVec 32), 2 ≤ i.toNat ∧ i.toNat ≤ s.core.tmp_len ∧
        S13Tpi s.core.tmp t2 s.core.tmp_len ∧
        (∀ k, 1 ≤ k → k < i.toNat →
          s13Lv s.core.lvl (t2[k]?.getD 0#32) ≤ s13Lv s.core.lvl (t2[1]?.getD 0#32)) ∧
        (FullMem c { s with core := { s.core with tmp := t2 } } ⋆ Rext) m2)
      (fun (i, ()) _ => s.core.tmp_len - i.toNat) ?_ ?_
    · intro J hJ
      c0_steps
      refine hJ _ m ⟨s.core.tmp, by decide, htl_ge2, s13Tpi_refl _ _, fun k hk1 hk2 => ?_, hm⟩
      have hk : k = 1 := by have : (2 : BitVec 64).toNat = 2 := rfl; omega
      subst hk; exact Nat.le_refl _
    intro J ⟨i, ⟨⟩⟩ m2 ⟨t2, hi2, hin, ht2, hmax2, hm2⟩ ih
    have ht2l := ht2.1
    have hll := hcl.lvl_len
    c0_clean; c0_split
    · exact s13_ins_body_wp J (by bv_omega) hi2 ht2 hmax2 hm2 htl_cv hcv_le htmp_len_arr hll hmv
        (fun k hk => (htmp_vals k hk).1) (fun i' m' h1 h2 => ih (i', ()) m' h1 h2)
    have hi_eq : i.toNat = s.core.tmp_len := by bv_omega
    obtain ⟨hsw_iff, hsw_mem, hsw_nd, hsw_0, ⟨jw, hjw1, hjwn, hjw_eq⟩, hle_all⟩ :=
      s13_final_props (lvl := s.core.lvl) ht2 htl_ge2 (by omega) huip_0 htmp_nd
        (fun k hk1 hk2 => hmax2 k hk1 (by omega))
    have h1_t : 1 < t2.length := by omega
    have hsw_1 : t2[1]? = some (t2[1]'h1_t) := List.getElem?_eq_getElem h1_t
    have hwm_getD : t2[1]?.getD 0#32 = t2[1]'h1_t := by rw [hsw_1, Option.getD_some]
    rw [hwm_getD] at hjw_eq
    have hmi_post := htmp_lvls jw hjw1 hjwn
    have hwm_vals := htmp_vals jw hjwn
    rw [hjw_eq] at hmi_post hwm_vals
    have hwm_lt : (t2[1]'h1_t).toNat < 2 * s.core.cur_vars := hwm_vals.1
    have hwm_v_lt : (t2[1]'h1_t).toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
    have hml_pos : 0 < (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat := hmi_post.1
    have hml_lt : (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat < s.core.cur_level :=
      hmi_post.2
    have hidx1_lt : ((t2[1]'h1_t).setWidth 64 >>> 1).toNat < s.core.lvl.length := by
      rw [s13_lshr1]; exact hwm_v_lt
    have hml_get : (s.core.lvl[((t2[1]'h1_t).setWidth 64 >>> 1).toNat]'hidx1_lt).toNat =
        (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat :=
      (s13Lv_of_idx (s13_lshr1 _) hidx1_lt).symm
    c0_clean; c0_to_group
    refine wp_join_group (ts := [i64]) (fun (ml_v, ()) m_ml =>
        m_ml = m2 ∧ ml_v =
          BitVec.ofNat 64 (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat) ?_ ?_
    rotate_left
    · intro Jml hJml; c0_split
      c0_steps
      have hml_set : BitVec.setWidth 64
          (s.core.lvl[((t2[1]'h1_t).setWidth 64 >>> 1).toNat]'hidx1_lt) =
          BitVec.ofNat 64 (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat := by
        apply BitVec.eq_of_toNat_eq
        rw [bv32_setWidth64_toNat, hml_get, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hml_set]
      exact hJml _ m2 ⟨rfl, rfl⟩
    rintro _ ⟨ml_v, ⟨⟩⟩ m_ml ⟨hm_ml, rfl⟩
    rw [hm_ml]
    have hwm_get : ∀ j, 1 ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat := fun j hj1 hj2 => by
      have := hle_all j hj1 hj2; unfold s13Lv at this; rwa [hwm_getD] at this
    clear ih hmax2 hi2 hin hi_eq hc hml_get hidx1_lt hwm_v_lt hmi_post hwm_vals hle_all hwm_getD
    generalize t2[1]'h1_t = wm at hsw_1 hwm_lt hml_pos hml_lt hjw_eq hwm_get ⊢
    generalize (s.core.lvl[wm.toNat / 2]?.getD 0#32).toNat = max_lvl at hml_pos hml_lt hwm_get ⊢
    let tmp_sw := t2
    let s_sw : FullState := { s with core := { s.core with tmp := tmp_sw } }
    have hm_sw' : (FullMem c s_sw ⋆ Rext) m2 := hm2
    have hsw_len : s_sw.LengthsOk c :=
      ⟨{ hcl with tmp_len_arr := by simp [s_sw, tmp_sw, ht2l, htmp_len_arr] }, hs.1.scratch_ok⟩
    have hsw_inv : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s_sw :=
      ⟨hsw_len, FullLearnAnaHelpers.FullOtfsWitnessInv.with_tmp hw tmp_sw, hs.2.2.1,
        hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    have hsw_inv_c : FullOtfsInvW c F0 F_cur s_sw := s13_laOtfsInv_to_canon hsw_inv
    have hent_sw : (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((tmp_sw.take s.core.tmp_len).map BitVec.toNat)) :=
      entails_of_mem_or_false hent fun l hl => Or.inl ((hsw_iff l).mpr hl)
    have hsw_lits_lt : ∀ l ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
        l < 2 * s.core.cur_vars := fun l hl => by
      rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
      · exact huip_lt
      · rw [← hjeq]; exact (htmp_vals j hj2).1
    have htmp_sw_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars := by
      intro k hk
      have hlen_sw : k < tmp_sw.length := by simp [tmp_sw, ht2l, htmp_len_arr]; omega
      have hmem : (tmp_sw[k]?.getD 0#32).toNat ∈
          (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
        rw [List.mem_map]
        refine ⟨tmp_sw[k]'hlen_sw, List.mem_iff_getElem.mpr ⟨k, by
          rw [List.length_take]; omega, by rw [List.getElem_take]⟩, ?_⟩
        rw [List.getElem?_eq_getElem hlen_sw, Option.getD_some]
      have := hsw_lits_lt _ hmem; omega
    c0_to_group; c0_call hDnl
    have hml_bv64 : (BitVec.ofNat 64 max_lvl).toNat = max_lvl := bv64_ofNat_toNat (by omega)
    refine ⟨c, s_sw, Rext, rfl, hsw_len, by dsimp [s_sw]; omega, hm_sw', fun nlvl _ hnlvl_pos => ?_⟩
    obtain ⟨hnlvl_ge, hnlvl_lt⟩ :=
      hnlvl_pos hcur_pos (by dsimp [s_sw]; rw [hml_bv64]; exact hml_lt)
    dsimp only [s_sw] at hnlvl_ge hnlvl_lt
    rw [hml_bv64] at hnlvl_ge
    c0_to_group; c0_call hBt
    refine ⟨c, s_sw, Rext, rfl, hsw_len, by dsimp [s_sw]; omega,
      fun _ => by have := hcl.cur_vars_le; omega, hsw_inv.2.1.trail_lits_lt, hm_sw', ?_⟩
    intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt m_bt s_bt
      hbt_len _ _ hbt_cl hbt_pres _ _ hbt_keep _ hbt_otfs hm_bt
    have hcl_bt : cl_bt = nlvl.toNat := by dsimp [s_sw] at hbt_cl; omega
    have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hsw_inv_c.2.1 hnlvl_lt
    have hbt_sparse := s13_laSparse_to_canon
      (fullBacktrack_preserves_fullSparseW hsw_inv hbt_len hbt_w rfl rfl rfl rfl rfl hbt_pres.1)
    have ⟨hkeep_v, hkeep_l⟩ := hbt_keep ⟨F0, F_cur, Or.inr hsw_inv_c.2.1⟩
    have hlow_on_bt : ∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = (s.core.tmp[j]?.getD 0#32).toNat ^^^ 1 ∧
          (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
      intro j hj1 hj2
      have hjv := htmp_vals j hj2
      have hle_ml : (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          max_lvl := hwm_get j hj1 hj2
      have hle_nl : (s_sw.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          nlvl.toNat := by dsimp only [s_sw]; omega
      have hv_bt : vals_bt[(s.core.tmp[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
        rw [hkeep_v _ hjv.1, ite_eq_left hle_nl]; exact hjv.2
      have hl_bt : (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        obtain ⟨i0, hi0, hi0_eq⟩ := (hsw_inv.2.1.vals_false_iff _ hjv.1).mp hjv.2
        have hdiv : (s_sw.core.trl[i0]?.getD 0#32).toNat / 2 =
            (s.core.tmp[j]?.getD 0#32).toNat / 2 := by rw [hi0_eq, fullInv_var_xor1]
        have hl_eq := hkeep_l i0 hi0
        rw [hdiv] at hl_eq; rw [hl_eq, ite_eq_left hle_nl]; exact hle_ml
      obtain ⟨idx, hidx, heq⟩ := (hbt_w.vals_false_iff _ hjv.1).mp hv_bt
      exact ⟨idx, hidx, heq, hl_bt⟩
    have hwm_on_bt : ∃ idx < te_bt,
        (trl_bt[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
        (lvl_bt[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
      simpa only [hjw_eq] using hlow_on_bt jw hjw1 hjwn
    have hlow_bt : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
        q = uip.toNat ∨ ∃ idx < te_bt,
          (trl_bt[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
          (lvl_bt[q / 2]?.getD 0#32).toNat ≤ max_lvl := fun q hq => by
      rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
      · exact Or.inl rfl
      · right; rw [← hjeq]; exact hlow_on_bt j hj1 hj2
    clear hDnl hBt htmp_vals htmp_lvls hent hm_sw' hm2 hbt_keep hbt_otfs hkeep_v hkeep_l
      hsw_mem hlow_on_bt
    have hbt_pre : S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_bt :=
      ⟨hbt_sparse, hcl_bt, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, hbt_pres.2.2.1⟩
    refine s13_learn_pre_gc_wp hDefrag hRedM6 hcfg hext hbt_pre huip_in huip_0 huip_lt
      (by omega) hnlvl_lt
      (fullM6HdrMem_unfocus_full hm_bt) hQ fun ext_gc s_gc m_gc hext_gc hgc_pre hm_gc => ?_
    have _hm_gcf := fullM6HdrMem_focus_full hm_gc
    c0_to_group
    refine s13_add_call_wp hAddCl htl_ge2 htl_cv hsw_0 hsw_1 hsw_lits_lt hsw_nd hent_sw hext_gc
      hgc_pre hm_gc fun new_ref0 s_ac0 m_ac0 h0_pre h0_nr hm_ac0 => ?_
    c0_to_group
    refine wp_loop_inv
      (fun (new_ref64, step, ()) mL =>
        step.toNat ≤ 3 ∧
        ∃ (ext_lp : List (BitVec 64)) (s_lp : FullState),
          M6HdrExtOk ext_lp ∧
          S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_lp ∧
          S13NrSpec F_cur s uip wm tmp_sw s_lp new_ref64 ∧
          (FullM6HdrMem c ext_lp s_lp ⋆ R) mL)
      (fun (_, step, ()) _ => 3 - step.toNat)
      (fun JL hLoop =>
        hLoop (new_ref0, 0#64, ()) m_ac0
          ⟨Nat.zero_le _, ext_gc, s_ac0, hext_gc, h0_pre, h0_nr, hm_ac0⟩)
      (fun JL (new_ref64, step, ()) mL
          ⟨hstep_le, ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩ hLoop => ?_)
    refine wp_join_group (ts := [])
      (fun () m_ex => ∃ ext_ex s_ex,
        M6HdrExtOk ext_ex ∧
        S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_ex ∧
        S13NrSpec F_cur s uip wm tmp_sw s_ex new_ref64 ∧
        (FullM6HdrMem c ext_ex s_ex ⋆ R) m_ex)
      ?_ ?_
    · rintro _ ⟨⟩ m_ex ⟨ext_ex, s_ex, hext_ex, hex_pre, hex_nr, hm_ex⟩
      simp only [Blocks.get]
      refine (congrArg (fun e => wp Γ Q X e m_ex) ?_).mpr
        (s13_learn_post_ac_m6_wp hAsgn hEsub hext_ex hex_pre hex_nr hml_pos hnlvl_ge hnlvl_lt
          hsw_1 htl_ge2 htl_cv huip_lt hwm_lt htmp_sw_lt hwm_on_bt hlow_bt hm_ex hQ)
      unfold s13PostAcExpr; rfl
    · intro J_post hJ_post
      clear hAsgn hEsub hwm_on_bt hlow_bt
      have _hmLf := fullM6HdrMem_focus_full hmL
      c0_split
      · c0_split
        · have hstep_lt : step.toNat < 3 := by c0_bound
          have hstep1 : (step + 1#64).toNat = step.toNat + 1 := by c0_bound
          c0_to_group
          refine wp_join_group (ts := [])
            (fun () m_pre => ∃ ext_pre s_pre,
              M6HdrExtOk ext_pre ∧
              S13AddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt s_pre ∧
              (FullM6HdrMem c ext_pre s_pre ⋆ R) m_pre)
            ?_ ?_
          · rintro _ ⟨⟩ m_pre ⟨ext_pre, s_pre, hext_pre, hpre_ok, hm_pre⟩
            have _hm_pref := fullM6HdrMem_focus_full hm_pre
            have _hpre_len := hpre_ok.1.1
            simp only [Blocks.get]
            c0_hsteps
            refine s13_add_call_wp hAddCl htl_ge2 htl_cv hsw_0 hsw_1 hsw_lits_lt hsw_nd hent_sw
              hext_pre hpre_ok hm_pre fun nr' sac' mac' hsac' hnr' hmac' => ?_
            c0_hsteps
            exact hLoop (nr', step + 1#64, ()) mac' (by dsimp only; rw [hstep1]; omega)
              ⟨by omega, ext_pre, sac', hext_pre, hsac', hnr', hmac'⟩
          · intro J1 hJ1
            exact s13_learn_retry_step_wp hDefrag hRedM6
              (fun _ m Q X hs => hRedPurge _ m Q X (fullReducePurgeC0Spec_of_full hs))
              hcfg hext_lp hlp_pre huip_lt (by omega) hnlvl_lt hmL hQ J1
              (fun m_pre h => hJ1 () m_pre h)
        · c0_hsteps; exact hJ_post () mL ⟨ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩
      · c0_hsteps; exact hJ_post () mL ⟨ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end
