/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Vivify
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.WpSimplify0
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics

/-!
# Kissat `full_viv_commit_m6` Weakest-Precondition Proof (`Proof.Vivify.WpCommit`)

Modular UNSAT-sound WP proof for `full_viv_commit_m6_body`:
- `commit_backtrack_zero_wp` / `commit_backtrack_gt_wp`: conditional chronological backtrack.
- `commit_nsz0_wp`: empty-clause (`olen = 0`) UNSAT witness + backtrack + `inconsistent := 1`.
- `commit_nsz12_wp`: unit/binary (`1 ≤ olen ≤ 2`) unwatch + mark garb + decr + `add_unit`/`add_bin`.
- `commit_copy_loop_wp` / `commit_flag_loop_wp` / `commit_oom_wp`: in-place shrink (`3 ≤ olen`).
- `commit_nsz_ge3_wp` & public `full_viv_commit_m6_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open Kraken.Bedrock2.Test
open VivTactics
open scoped FullArenaTactics VivTactics

section

/-! ## 1. Shared state preservation & backtrack helpers -/

private def VivCommitPres (s0 s' : FullState) : Prop :=
  s'.core.cur_vars = s0.core.cur_vars ∧
  s'.core.arena_len = s0.core.arena_len ∧
  s'.core.probing = s0.core.probing ∧
  s'.core.fuel = s0.core.fuel ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s0 ∧
  s'.scratch.red_refs = s0.scratch.red_refs ∧
  s'.scratch.tarjan_reach = s0.scratch.tarjan_reach

private theorem VivCommitPres.refl (s : FullState) : VivCommitPres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem VivCommitPres.trans {s1 s2 s3 : FullState}
    (h12 : VivCommitPres s1 s2) (h23 : VivCommitPres s2 s3) : VivCommitPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

private theorem VivCommitPres.of_refs {s1 s2 : FullState}
    (h1 : s2.core.cur_vars = s1.core.cur_vars) (h2 : s2.core.arena_len = s1.core.arena_len)
    (h3 : s2.core.probing = s1.core.probing) (h4 : s2.core.fuel = s1.core.fuel)
    (h5 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1)
    (h6 : s2.scratch.red_refs = s1.scratch.red_refs)
    (h7 : s2.scratch.tarjan_reach = s1.scratch.tarjan_reach) : VivCommitPres s1 s2 :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

private abbrev VivCommitQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
    FullSparseInvW c F0 F_cur s' → VivCommitPres s0 s' →
    (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem viv_clause_bd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) :
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
  have hwf := (hsp.2.1.arena.refs_wf cref href).2.2
  have hle := hsp.1.core_ok.arena_len_le
  have har := hsp.1.core_ok.arena_len_arr
  omega

private theorem viv_cur_level_lt_u64 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) :
    s.core.cur_level ≤ c.max_vars ∧ s.core.cur_level < 2 ^ 64 := by
  have h1 := hsp.2.1.cur_level_le
  have h2 := hsp.1.core_ok.trail_end_le
  have h3 := hsp.1.core_ok.cur_vars_le
  have h4 := c.hmaxv
  have hdb : dimacsBound = 2 ^ 28 := rfl
  omega

private theorem commit_sparseW_of_core_pres {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur s' := by
  have hmc : FullLitMarksClear c s' :=
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
  have hnd : FullArenaVarsNodup s' := fun r hr hg => by
    have hr0 : r ∈ fullArenaClauseRefs s := hrefs ▸ hr
    have hg0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hg ⊢
      rw [← har]; exact hg
    have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hlits]; exact hsp.2.2.2.1 r hr0 hg0
  have hxs : FullExtScratchOk c s' :=
    FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll, hel⟩ fun r hr => by rw [hrefs]; exact hr
  exact ⟨hlen', hw', hmc, hnd, hxs, hdm.trans hsp.2.2.2.2.2⟩

private theorem commit_backtrack_call_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {target : BitVec 64} {J : Cont []}
    {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (ht_lt : target.toNat < s.core.cur_level)
    (hmv : target.toNat < c.max_vars) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = target.toNat →
      VivCommitPres s s' → s'.core.arena = s.core.arena →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → J () m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
        (Arg.var c.hdr, Arg.var target, ()) fun _ => Expr.jump J ())
      m := by
  have hcl_lt := (viv_cur_level_lt_u64 hsp).2
  viv_call hBt
  refine ⟨c, s, R, rfl, hsp.1, hcl_lt, fun _ => hmv, hsp.2.1.trail_lits_lt, hm, ?_⟩
  rintro va' lv' rs' tr' tp' te' pr' cl' un' sc' m' _
    hlen' _ _ hcl' hpr' ⟨_, _, _, _, _, _, _, _, _, hsc'⟩ _ _ hw_bt _ hmb
  let sb : FullState :=
    { s with
      core := { s.core with vals := va', lvl := lv', rsns := rs', trl := tr', trail_pos := tp',
                            trail_end := te', propagated := pr', cur_level := cl',
                            unassigned := un' }
      scratch := sc' }
  have hsp_b : FullSparseInvW c F0 F_cur sb :=
    viv_sparseW_of_backtrack hsp (target_lvl := target.toNat) (Nat.le_of_lt ht_lt)
      hlen' ⟨hpr'.1, hpr'.2.1, hpr'.2.2.1, hpr'.2.2.2.1, hpr'.2.2.2.2.1,
             hpr'.2.2.2.2.2.1, hpr'.2.2.2.2.2.2.1, hpr'.2.2.2.2.2.2.2⟩
      (hw_bt F0 F_cur hsp.2.1 (Nat.le_of_lt ht_lt))
  have hcl_eq : sb.core.cur_level = target.toNat := by
    change cl' = target.toNat; rw [hcl']; omega
  have hpres : VivCommitPres s sb :=
    VivCommitPres.of_refs rfl rfl rfl rfl rfl (by simp [sb, hsc']) (by simp [sb, hsc'])
  viv_hfast
  exact hk sb m' hsp_b hcl_eq hpres rfl (by simp [sb, hsc']) hmb

private def commitBacktrackZeroExpr (h : Val i64) (J : Cont []) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var h, Arg.imm 160, ()) }
    fun p1 =>
  Expr.load i64 (Arg.var p1.fst) fun ld =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (by decide),
              args := (Arg.var ld, Arg.imm 0, ()) } fun p2 =>
  Expr.jnz (Arg.var p2.fst)
    (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var h, Arg.imm 0, ()) fun _ => Expr.jump J ())
    (Expr.jump J ())

private theorem commit_backtrack_zero_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {J : Cont []} {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      VivCommitPres s s' → s'.core.arena = s.core.arena →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → J () m') :
    wp Γ Q X (commitBacktrackZeroExpr c.hdr J) m := by
  dsimp only [commitBacktrackZeroExpr]
  viv_steps
  · have hcl_ne : s.core.cur_level ≠ 0 := by
      intro hz; exact hc (by simp [hz])
    have ⟨hcl_le, _⟩ := viv_cur_level_lt_u64 hsp
    have h0_lt_mv : (0#64 : BitVec 64).toNat < c.max_vars := by simp; omega
    exact commit_backtrack_call_wp Γ hBt hsp (by simp; omega) h0_lt_mv hm
      fun s' m' hsp' hcl' hpr' har' hws2' hm' => hk s' m' hsp' hcl' hpr' har' hws2' hm'
  · have hcl0 : s.core.cur_level = 0 := by
      have ⟨_, hlt⟩ := viv_cur_level_lt_u64 hsp
      have hbv : BitVec.ofNat 64 s.core.cur_level = 0#64 := hc
      have := congrArg BitVec.toNat hbv
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using this
    exact hk s m hsp hcl0 (VivCommitPres.refl s) rfl rfl hm

private def commitBacktrackGtExpr (h : Val i64) (nl : Val i64) (J : Cont []) :
    Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var h, Arg.imm 160, ()) }
    fun p1 =>
  Expr.load i64 (Arg.var p1.fst) fun ld =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
              args := (Arg.var ld, Arg.var nl, ()) } fun p2 =>
  Expr.jnz (Arg.var p2.fst)
    (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var h, Arg.var nl, ()) fun _ => Expr.jump J ())
    (Expr.jump J ())

private theorem commit_backtrack_gt_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {nl : BitVec 64} {J : Cont []}
    {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hmv : nl.toNat < c.max_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → VivCommitPres s s' →
      s'.core.arena = s.core.arena → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → J () m') :
    wp Γ Q X (commitBacktrackGtExpr c.hdr nl J) m := by
  dsimp only [commitBacktrackGtExpr]
  viv_steps
  · have hlt : nl.toNat < s.core.cur_level := by
      have ⟨_, hcl64⟩ := viv_cur_level_lt_u64 hsp
      rw [Nat.mod_eq_of_lt hcl64] at hc
      exact hc
    exact commit_backtrack_call_wp Γ hBt hsp hlt hmv hm
      fun s' m' hsp' _ hpr' har' hws2' hm' => hk s' m' hsp' hpr' har' hws2' hm'
  · exact hk s m hsp (VivCommitPres.refl s) rfl rfl hm

/-! ## 2. Short-clause commit cases (`olen = 0` and `1 ≤ olen ≤ 2`) -/

private theorem commit_nsz0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [])) :
    F0.Unsat ∧ (cnfOfClauses F_cur).Unsat := by
  have huf : (cnfOfClauses F_cur).Unsat := fun τ => by
    by_cases hsat : (cnfOfClauses F_cur).eval τ = true
    · have h := (clause_sat_cnfClause_iff τ []).mp (CNF.entails_clause_def.mp hent τ hsat)
      simp at h
    · simpa [CNF.Sat] using hsat
  exact ⟨hsp.2.1.ext_sound.2 huf, huf⟩

private theorem commit_nsz0_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause []))
    (hm : (FullMem c s ⋆ R) m) (hQ : VivCommitQ c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.group
        (fun _ =>
          Blocks.cons
            (fun (_ : Tup Val []) =>
              Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p =>
              Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst) (Expr.ret (Arg.imm 20, ())))
            Blocks.nil)
        fun Js => commitBacktrackZeroExpr c.hdr Js.fst)
      m := by
  have ⟨hf0_uns, hfcur_uns⟩ := commit_nsz0_unsat hsp hent
  viv_to_group
  refine wp_join0 (fun m2 => ∃ s2, FullSparseInvW c F0 F_cur s2 ∧ VivCommitPres s s2 ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro _ m2 ⟨s2, hsp2, hpr2, hm2⟩
    viv_hfast
    have hsp3 := fullSparseInvW_with_inconsistent hsp2 hfcur_uns
    have hpr3 : VivCommitPres s { s2 with core := { s2.core with inconsistent := 1#64 } } :=
      hpr2.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    exact hQ 20#64 _ _ hsp3 hpr3 (Or.inr (Or.inr rfl)) (fun _ => hf0_uns) (by assumption)
  · intro J hJ
    exact commit_backtrack_zero_wp Γ hBt hsp hm fun s2 m2 hsp2 _ hpr2 _ _ hm2 =>
      hJ m2 ⟨s2, hsp2, hpr2, hm2⟩

private def commitNsz12TailExpr (c : FullCfg) (olen : Val i32) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
              args := (Arg.var olen, Arg.imm 1, ()) } fun p37 =>
  Expr.jnz (Arg.var p37.fst)
    (Expr.group
      (fun Js => Blocks.cons (fun (p : Tup Val [i64]) => Expr.ret (Arg.var p.fst, ())) Blocks.nil)
      fun Js =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p38 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                  args := (Arg.var p38.fst, Arg.imm 4, ()) }
        fun p39 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.pWorkStk2, Arg.var p39.fst, ()) } fun p40 =>
      Expr.load i32 (Arg.var p40.fst) fun ld =>
      Expr.call (as := [i64, i32]) (bs := [Ty.bool]) "full_add_unit"
        (Arg.var c.hdr, Arg.var ld, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.jump Js.fst (Arg.imm 1, ())) (Expr.jump Js.fst (Arg.imm 20, ())))
    (Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p38 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p38.fst, Arg.imm 4, ()) }
      fun p39 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pWorkStk2, Arg.var p39.fst, ()) } fun p40 =>
    Expr.load i32 (Arg.var p40.fst) fun ld =>
    Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p41 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p41.fst, Arg.imm 4, ()) }
      fun p42 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pWorkStk2, Arg.var p42.fst, ()) } fun p43 =>
    Expr.load i32 (Arg.var p43.fst) fun ld7 =>
    Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin_m6"
      (Arg.var c.hdr, Arg.var ld, Arg.var ld7, ()) fun p =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (by decide),
                args := (Arg.var p.fst, Arg.imm 20, ()) } fun p44 =>
    Expr.jnz (Arg.var p44.fst) (Expr.ret (Arg.imm 20, ()))
      (Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (by decide),
                   args := (Arg.var p.fst, Arg.imm 2, ()) } fun p =>
      Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 2, ())) (Expr.ret (Arg.imm 1, ()))))

private theorem commit_nsz12_tail_wp (Γ : Env)
    (hUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hBin : Γ.Has "full_add_bin_m6" fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 sd : FullState}
    {R : Mem 64 → Prop} {md : Mem 64} {olen : BitVec 32} {Q : Post [i64]} {X : XPost}
    (hsp_d : FullSparseInvW c F0 F_cur sd) (hcl_d : sd.core.cur_level = 0)
    (hpr_d : VivCommitPres s0 sd) (hm_d : (FullMem c sd ⋆ R) md)
    (hne0 : olen ≠ 0#32) (hle2 : olen.toNat ≤ 2) (hol_mv : olen.toNat ≤ c.max_vars)
    (hlits : ∀ i < olen.toNat, (sd.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * sd.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((sd.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitNsz12TailExpr c olen) md := by
  have hws2_0 : 0 < sd.scratch.work_stk2.length := by
    have := hsp_d.1.scratch_ok.work_stk2_len
    have hnz : olen.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  dsimp only [commitNsz12TailExpr]
  viv_steps
  · have hol1 : olen = 1#32 := hc
    have hlt0 : (sd.scratch.work_stk2[0]'hws2_0).toNat < 2 * sd.core.cur_vars := by
      have h := hlits 0 (by rw [hol1]; decide)
      rwa [List.getElem?_eq_getElem hws2_0, Option.getD_some] at h
    have hent0 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(sd.scratch.work_stk2[0]'hws2_0).toNat]) := by
      have htk : sd.scratch.work_stk2.take 1 = [sd.scratch.work_stk2[0]'hws2_0] :=
        List.ext_getElem (by simp [Nat.min_eq_left hws2_0]) fun i hi _ => by
          rw [List.length_take, Nat.min_eq_left hws2_0] at hi
          cases i with | zero => simp | succ => omega
      simpa [hol1, htk] using hent
    viv_call hUnit
    refine ⟨c, F0, F_cur, sd, R, rfl, hsp_d.1, hsp_d.2.1, fun _ => hent0, hm_d, ?_⟩
    rintro ok va' fl' lv' rs' tr' tp' te' pr' cl' un' uf' inc' ph' ta' ba' pt' pb' hp' ps'
      hl' qsi' qss' mu _ hlen_u hw_u hcl_u hok_f _ hmu
    let su : FullState :=
      { core := { sd.core with vals := va', flags := fl', lvl := lv', rsns := rs', trl := tr',
                               trail_pos := tp', trail_end := te', propagated := pr',
                               cur_level := cl', unassigned := un', unflushed := uf',
                               inconsistent := inc' }
        scratch := { sd.scratch with phases := ph', target_assigned := ta',
                                     best_assigned := ba', phases_target := pt',
                                     phases_best := pb', heap := hp', pos := ps', heap_len := hl',
                                     q_search_idx := qsi', q_search_stamp := qss' } }
    have hsp_u : FullSparseInvW c F0 F_cur su :=
      commit_sparseW_of_core_pres hsp_d hlen_u hw_u rfl rfl rfl rfl rfl rfl rfl
    have hpr_u : VivCommitPres s0 su :=
      hpr_d.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    viv_steps
    · exact hQ 1#64 su mu hsp_u hpr_u (Or.inl rfl) (fun h => by cases h) hmu
    · have huns : F0.Unsat := (hok_f hlt0 (by cases ok <;> simp_all)).1
      exact hQ 20#64 su mu hsp_u hpr_u (Or.inr (Or.inr rfl)) (fun _ => huns) hmu
  · have hol2 : olen = 2#32 := by
      have hn1 : olen.toNat ≠ 1 := fun h1 => hc (BitVec.eq_of_toNat_eq (by simpa using h1))
      have hn0 : olen.toNat ≠ 0 := fun h0 => hne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      exact BitVec.eq_of_toNat_eq (by change olen.toNat = 2; omega)
    have hmv2 : 1 < sd.scratch.work_stk2.length := by
      have := hsp_d.1.scratch_ok.work_stk2_len
      have h2 : olen.toNat = 2 := by simpa using congrArg BitVec.toNat hol2
      omega
    viv_hfast
    have hent2 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(sd.scratch.work_stk2[0]'hws2_0).toNat,
                    (sd.scratch.work_stk2[1]'hmv2).toNat]) := by
      have h2_le : 2 ≤ sd.scratch.work_stk2.length := by omega
      have htk : sd.scratch.work_stk2.take 2 =
          [sd.scratch.work_stk2[0]'hws2_0, sd.scratch.work_stk2[1]'hmv2] :=
        List.ext_getElem (by simp [Nat.min_eq_left h2_le]) fun i hi _ => by
          rw [List.length_take, Nat.min_eq_left h2_le] at hi
          rcases i with _ | _ | _ <;> first | omega | simp
      simpa [hol2, htk] using hent
    viv_call hBin
    refine ⟨c, F0, F_cur, sd, R, rfl, hsp_d.1, hsp_d.2.1, hcl_d, fun _ _ => hent2, hm_d, ?_⟩
    rintro rb va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' wl' wu' nb' oo' ic' ph' wso'
      mb _ hlen_b hw_b hrb h20 _ hmb
    let sb : FullState :=
      { core := { sd.core with vals := va', flags := fl', lvl := lv', rsns := rs', trl := tr',
                               trail_pos := tp', trail_end := te', unassigned := un',
                               unflushed := uf', wvec := wv', wstk := ws', wlen := wl',
                               wusable := wu', num_binary := nb', oom := oo', inconsistent := ic' }
        scratch := { sd.scratch with phases := ph', wsort := wso' } }
    have hsp_b : FullSparseInvW c F0 F_cur sb :=
      commit_sparseW_of_core_pres hsp_d hlen_b hw_b rfl rfl rfl rfl rfl rfl rfl
    have hpr_b : VivCommitPres s0 sb :=
      hpr_d.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    viv_steps
    · exact hQ 20#64 sb mb hsp_b hpr_b (Or.inr (Or.inr rfl)) (fun _ => (h20 hc).1) hmb
    · exact hQ 2#64 sb mb hsp_b hpr_b (Or.inr (Or.inl rfl)) (fun h => by cases h) hmb
    · exact hQ 1#64 sb mb hsp_b hpr_b (Or.inl rfl) (fun h => by cases h) hmb

private theorem viv_unwatch_one_wp (Γ : Env)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {lit cref : BitVec 32}
    {k : Tup Val [] → Expr Val Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ wv' ws' wu' m',
      let s' := { s with core := { s.core with wvec := wv', wstk := ws', wusable := wu' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
      (Arg.var c.hdr, Arg.var lit, Arg.var cref, ()) k) m := by
  viv_call hUnwatch
  refine ⟨c, s, R, rfl, hsp.1, viv_watchLayout_of_sparse hsp, hm,
    fun wv' ws' wu' m' hlen' _ hmw' hm' => ?_⟩
  let hw := hsp.2.1
  exact hk wv' ws' wu' m' ⟨hlen',
    { hw with
      arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
        hw.arena.lits_lt, hw.arena.entails⟩
      watches := hmw' F_cur hw.watches }, hsp.2.2⟩ hm'

private def commitNsz12Expr (c : FullCfg) (cref olen hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun _ =>
      Blocks.cons
        (fun (_ : Tup Val []) =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
            fun p17 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p17.fst, Arg.imm 3, ()) } fun p18 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p18.fst, Arg.imm 4, ()) } fun p19 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p19.fst, ()) } fun p20 =>
          Expr.load i32 (Arg.var p20.fst) fun ld5 =>
          Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
            (Arg.var c.hdr, Arg.var ld5, Arg.var cref, ()) fun _ =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
            fun p22 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p22.fst, Arg.imm 4, ()) } fun p23 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p23.fst, Arg.imm 4, ()) } fun p24 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p24.fst, ()) } fun p25 =>
          Expr.load i32 (Arg.var p25.fst) fun ld6 =>
          Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
            (Arg.var c.hdr, Arg.var ld6, Arg.var cref, ()) fun _ =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
            fun p27 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p27.fst, Arg.imm 4, ()) } fun p28 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p28.fst, ()) } fun p29 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var hdr_v, Arg.imm 524288, ()) } fun p30 =>
          Expr.store (Arg.var p30.fst) (Arg.var p29.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p31 =>
            Expr.load i64 (Arg.var p31.fst) fun ld =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var ld, Arg.imm 3, ()) } fun p32 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var old_sz, ()) }
              fun p33 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p32.fst, Arg.var p33.fst, ()) } fun p34 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p35 =>
            Expr.store (Arg.var p34.fst) (Arg.var p35.fst)
              (Expr.group
                (fun _ => Blocks.cons
                  (fun (_ : Tup Val []) => commitNsz12TailExpr c olen) Blocks.nil)
                fun Js => simplifyDecrExpr c.hdr hdr_v Js.fst)))
        Blocks.nil)
    fun Js => commitBacktrackZeroExpr c.hdr Js.fst

private theorem commit_nsz12_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hBin : Γ.Has "full_add_bin_m6" fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s1 : FullState}
    {R : Mem 64 → Prop} {m1 : Mem 64} {cref olen old_sz : BitVec 32}
    {Q : Post [i64]} {X : XPost}
    (hsp1 : FullSparseInvW c F0 F_cur s1) (hpr1 : VivCommitPres s0 s1)
    (har1 : s1.core.arena = s0.core.arena) (hws2_1 : s1.scratch.work_stk2 = s0.scratch.work_stk2)
    (href : cref.toNat ∈ fullArenaClauseRefs s0)
    (_hng : fullArenaClauseGarb s0 cref.toNat = false)
    (hsz : fullArenaClauseSize s0 cref.toNat = old_sz.toNat)
    (hne0 : olen ≠ 0#32) (hle2 : olen.toNat ≤ 2) (hol_mv : olen.toNat ≤ c.max_vars)
    (_holt : olen.toNat < old_sz.toNat)
    (hlits : ∀ i < olen.toNat, (s0.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s0.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitNsz12Expr c cref olen (fullArenaHdr s0 cref.toNat) old_sz) m1 := by
  dsimp only [commitNsz12Expr]
  viv_to_group
  refine wp_join0 (fun m2 => ∃ s2, FullSparseInvW c F0 F_cur s2 ∧ s2.core.cur_level = 0 ∧
      VivCommitPres s0 s2 ∧ s2.core.arena = s0.core.arena ∧
      s2.scratch.work_stk2 = s0.scratch.work_stk2 ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro _ m2 ⟨s2, hsp2, hcl2, hpr2, har2, hws2_2, hm2⟩
    have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := by
      rw [hpr2.2.2.2.2.1]; exact href
    have hbd2 := viv_clause_bd hsp2 href2
    have hsz2 : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := by
      unfold fullArenaClauseSizeCore; rw [har2]; exact hsz
    have hdb : dimacsBound = 2 ^ 28 := rfl
    have har2_len := hsp2.1.core_ok.arena_len_arr
    have hc_ar : c.arena_cap < 2 * 2 ^ 28 := hdb ▸ c.harena
    have hsz2_ge2 : 2 ≤ fullArenaClauseSizeCore s2.core cref.toNat := by
      have : olen.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hc3_lt : (BitVec.setWidth 64 cref + 3).toNat < s2.core.arena.length := by bv_omega
    have hc4_lt : (BitVec.setWidth 64 cref + 4).toNat < s2.core.arena.length := by bv_omega
    viv_hfast_nogrp
    refine viv_unwatch_one_wp Γ hUnwatch hsp2 hm2 fun wv3 ws3 wu3 m3 hsp3 hm3 => ?_
    let s3 : FullState :=
      { s2 with core := { s2.core with wvec := wv3, wstk := ws3, wusable := wu3 } }
    viv_hfast_nogrp
    refine viv_unwatch_one_wp Γ hUnwatch hsp3 hm3 fun wv4 ws4 wu4 m4 hsp4 hm4 => ?_
    let s4 : FullState :=
      { s3 with core := { s3.core with wvec := wv4, wstk := ws4, wusable := wu4 } }
    have har4_len : s4.core.arena.length = s2.core.arena.length := rfl
    have hc0_lt : (BitVec.setWidth 64 cref).toNat < s4.core.arena.length := by bv_omega
    have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
    viv_hfast_nogrp
    let ag' := s4.core.arena_garbage + 3#64 + BitVec.setWidth 64 old_sz
    let ar_g := s4.core.arena.set cref.toNat (fullArenaHdr s4 cref.toNat ||| 524288#32)
    let sc_d (ni' nr' : BitVec 64) : FullCoreState :=
      { s4.core with arena := ar_g, arena_garbage := ag', num_irred := ni', num_redundant := nr' }
    let s_d (ni' nr' : BitVec 64) : FullState := { s4 with core := sc_d ni' nr' }
    refine wp_join0 (fun md => ∃ ni' nr', (FullMem c (s_d ni' nr') ⋆ R) md) ?_ ?_
    · rintro _ md ⟨ni', nr', hmd⟩
      have href4 : cref.toNat ∈ fullArenaClauseRefs s4 := href2
      have hsp_g := markGarb_hnonact_preserves_fullSparseW hsp4 href4
        (nonActiveReason_of_level0 hsp4.2.1 hcl2 cref.toNat) ag' ni' nr' s4.scratch.viv_cnt
      have hsp_d : FullSparseInvW c F0 F_cur (s_d ni' nr') := by
        simpa [s_d, sc_d, ar_g] using hsp_g.1
      have hrefs_d : fullArenaClauseRefs (s_d ni' nr') = fullArenaClauseRefs s4 := by
        have := hsp_g.2; simpa [s_d, sc_d, ar_g] using this
      have hpr_d : VivCommitPres s0 (s_d ni' nr') :=
        hpr2.trans (VivCommitPres.of_refs rfl rfl rfl rfl hrefs_d rfl rfl)
      have hws2_d : (s_d ni' nr').scratch.work_stk2 = s0.scratch.work_stk2 := hws2_2
      exact commit_nsz12_tail_wp Γ hUnit hBin hsp_d hcl2 hpr_d hmd hne0 hle2 hol_mv
        (fun i hi => by rw [hws2_d, hpr_d.1]; exact hlits i hi)
        (by rw [hws2_d]; exact hent) hQ
    · intro J2 hJ2
      have heq_hdr : fullArenaHdr s0 cref.toNat = fullArenaHdr s4 cref.toNat := by
        simp [fullArenaHdr, fullArenaHdrCore, s4, s3, har2]
      rw [heq_hdr]
      refine simplify_decr_wp
        (s_b := { s4 with core := { s4.core with arena := ar_g, arena_garbage := ag' } })
        Γ ?_ fun ni' nr' md hmd => hJ2 md ⟨ni', nr', hmd⟩
      have heq_ar : s4.core.arena.set (BitVec.setWidth 64 cref).toNat
          (fullArenaHdr s0 cref.toNat ||| 524288#32) = ar_g := by
        simp only [ar_g, hc0_idx, heq_hdr]
      rw [← heq_ar]
      exact (by assumption)
  · intro J hJ
    exact commit_backtrack_zero_wp Γ hBt hsp1 hm1 fun s2 m2 hsp2 hcl2 hpr2 har2 hws2 hm2 =>
      hJ m2 ⟨s2, hsp2, hcl2, hpr1.trans hpr2, har2.trans har1, hws2.trans hws2_1, hm2⟩

/-! ## 3. In-place shrink (`3 ≤ olen < old_sz`) helpers & main proof -/

private def commitOomExpr (h : Val i64) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var h, Arg.imm 760, ()) }
    fun p52 =>
  Expr.store (t := i64) (Arg.imm 1) (Arg.var p52.fst)
    (Expr.group (fun _ => Blocks.cons
        (fun (_ : Tup Val []) => Expr.ret (Arg.imm 2, ())) Blocks.nil)
      fun Js => commitBacktrackZeroExpr h Js.fst)

private theorem commit_oom_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 sw : FullState}
    {R : Mem 64 → Prop} {mw : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp_w : FullSparseInvW c F0 F_cur sw) (hpr_w : VivCommitPres s0 sw)
    (hm_w : (FullMem c sw ⋆ R) mw) (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitOomExpr c.hdr) mw := by
  dsimp only [commitOomExpr]
  viv_hfast_nogrp
  let so := { sw with core := { sw.core with oom := 1#64 } }
  have hsp_o : FullSparseInvW c F0 F_cur so := viv_with_oomW hsp_w 1#64
  have hpr_o : VivCommitPres s0 so :=
    hpr_w.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
  refine wp_join0 (fun m2 => ∃ s2, FullSparseInvW c F0 F_cur s2 ∧ VivCommitPres s0 s2 ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro _ m2 ⟨s2, hsp2, hpr2, hm2⟩
    viv_step
    exact hQ 2#64 s2 m2 hsp2 hpr2 (Or.inr (Or.inl rfl)) (fun h => by cases h) hm2
  · intro J hJ
    exact commit_backtrack_zero_wp Γ hBt hsp_o (by assumption) fun s2 m2 hsp2 _ hpr2 _ _ hm2 =>
      hJ m2 ⟨s2, hsp2, hpr_o.trans hpr2, hm2⟩

private def commitWatchPairExpr (c : FullCfg) (cref : Val i32) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p45 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p45.fst, Arg.imm 4, ()) }
    fun p46 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.pWorkStk2, Arg.var p46.fst, ()) } fun p47 =>
  Expr.load i32 (Arg.var p47.fst) fun ld =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p48 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p48.fst, Arg.imm 4, ()) }
    fun p49 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.pWorkStk2, Arg.var p49.fst, ()) } fun p50 =>
  Expr.load i32 (Arg.var p50.fst) fun ld7 =>
  Expr.group (fun _ => Blocks.cons
      (fun (_ : Tup Val []) => commitOomExpr c.hdr) Blocks.nil) fun Js =>
  Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
              args := (Arg.var ld7, Arg.imm 2147483647, ()) }
    fun p51 =>
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [Ty.bool]) "full_watch_push"
    (Arg.var c.hdr, Arg.var ld, Arg.var p51.fst, Arg.var cref, Arg.imm 2, ())
    fun p52 =>
  Expr.jnz (Arg.var p52.fst)
    (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                 args := (Arg.var ld, Arg.imm 2147483647, ()) } fun p53 =>
     Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [Ty.bool]) "full_watch_push"
       (Arg.var c.hdr, Arg.var ld7, Arg.var p53.fst, Arg.var cref, Arg.imm 2, ())
       fun p =>
     Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 1, ())) (Expr.jump Js.fst ()))
    (Expr.jump Js.fst ())

private theorem commit_watch_pair_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s_fl : FullState}
    {R : Mem 64 → Prop} {m_fl : Mem 64} {cref : BitVec 32} {Q : Post [i64]} {X : XPost}
    (hsp_fl : FullSparseInvW c F0 F_cur s_fl) (hpr_fl : VivCommitPres s0 s_fl)
    (href_fl : cref.toNat ∈ fullArenaClauseRefs s_fl) (hcref_lt : cref.toNat < 2147483648)
    (hmv2 : 2 ≤ c.max_vars)
    (hm_fl : (FullMem c s_fl ⋆ R) m_fl) (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitWatchPairExpr c cref) m_fl := by
  have hlen_ws2 : 1 < s_fl.scratch.work_stk2.length := by
    have := hsp_fl.1.scratch_ok.work_stk2_len; omega
  have hlen_ws2_0 : 0 < s_fl.scratch.work_stk2.length := by omega
  dsimp only [commitWatchPairExpr]
  viv_hfast_nogrp
  have hcref_ne : cref ≠ 4294967295#32 := fun he => by
    have := congrArg BitVec.toNat he; simp at this; omega
  refine wp_join0 (fun mw => ∃ sw, FullSparseInvW c F0 F_cur sw ∧ VivCommitPres s0 sw ∧
      (FullMem c sw ⋆ R) mw) ?_ ?_
  · rintro _ mw ⟨sw, hsp_w, hpr_w, hm_w⟩
    exact commit_oom_wp Γ hBt hsp_w hpr_w hm_w hQ
  · intro J hJ
    viv_hfast_nogrp
    viv_call hWpush
    refine ⟨c, s_fl, R, rfl, hsp_fl.1, viv_watchLayout_of_sparse hsp_fl,
      fun h => absurd h (by decide),
      fun _ => ⟨(bv32_mask_lo31_props _).2, hcref_ne⟩, hm_fl, ?_⟩
    rintro ok1 wv1 ws1 wl1 wu1 wso1 m1 _ hlen1 hlay1 hother1 hok1t hok1f hm1
    let sw1 : FullState :=
      { core := { s_fl.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 }
        scratch := { s_fl.scratch with wsort := wso1 } }
    have hsp1 : FullSparseInvW c F0 F_cur sw1 :=
      fullWatchPush_large_preserves_sparseInvW hsp_fl
        (bv32_mask_lo31_props _).1 hcref_lt href_fl hlen1 hlay1 hother1
        (fun h => let t := hok1t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
        (fun h => (hok1f h).1)
    have hpr1 : VivCommitPres s0 sw1 :=
      hpr_fl.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    viv_hfast_nogrp
    · viv_hfast_nogrp
      viv_call hWpush
      refine ⟨c, sw1, R, rfl, hsp1.1, viv_watchLayout_of_sparse hsp1,
        fun h => absurd h (by decide),
        fun _ => ⟨(bv32_mask_lo31_props _).2, hcref_ne⟩, hm1, ?_⟩
      rintro ok2 wv2 ws2 wl2 wu2 wso2 m2 _ hlen2 hlay2 hother2 hok2t hok2f hm2
      let sw2 : FullState :=
        { core := { sw1.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 }
          scratch := { sw1.scratch with wsort := wso2 } }
      have hsp2 : FullSparseInvW c F0 F_cur sw2 :=
        fullWatchPush_large_preserves_sparseInvW hsp1
          (bv32_mask_lo31_props _).1 hcref_lt href_fl hlen2 hlay2 hother2
          (fun h => let t := hok2t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
          (fun h => (hok2f h).1)
      have hpr2 : VivCommitPres s0 sw2 :=
        hpr1.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
      viv_hfast
      · exact hQ 1#64 sw2 m2 hsp2 hpr2 (Or.inl rfl) (fun h => by cases h) hm2
      · exact hJ m2 ⟨sw2, hsp2, hpr2, hm2⟩
    · exact hJ m1 ⟨sw1, hsp1, hpr1, hm1⟩

private def commitFlagLoopExpr (c : FullCfg) (pFl : Val i64) (olen : Val i32) (Js : Cont []) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Js_lp =>
      Blocks.cons
        (fun (p47 : Tup Val [i32]) =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                      args := (Arg.var p47.fst, Arg.var olen, ()) } fun pc =>
          Expr.jnz (Arg.var pc.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p47.fst, ()) } fun p1 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk2, Arg.var p2.fst, ()) } fun p3 =>
             Expr.load i32 (Arg.var p3.fst) fun ld7 =>
             Expr.group
               (fun Js_b =>
                 Blocks.cons
                   (fun (pb : Tup Val [i32]) =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                                 args := (Arg.var ld7, Arg.imm 1, ()) } fun p48 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p48.fst, ()) } fun p49 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p49.fst, Arg.imm 4, ()) } fun p50 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pFl, Arg.var p50.fst, ()) } fun p51 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                                 args := (Arg.var ld7, Arg.imm 1, ()) } fun p52 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p52.fst, ()) } fun p53 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p53.fst, Arg.imm 4, ()) } fun p54 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pFl, Arg.var p54.fst, ()) } fun p55 =>
                     Expr.load i32 (Arg.var p55.fst) fun ld =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                 args := (Arg.var ld, Arg.imm 8, ()) } fun p56 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                 args := (Arg.var p56.fst, Arg.imm 16, ()) } fun p57 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                 args := (Arg.var p57.fst, Arg.var pb.fst, ()) } fun pv =>
                     Expr.store (Arg.var pv.fst) (Arg.var p51.fst)
                       (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                    args := (Arg.var p47.fst, Arg.imm 1, ()) } fun pn =>
                        Expr.jump Js_lp.fst (Arg.var pn.fst, ())))
                   Blocks.nil)
               fun Js_b =>
               Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                           args := (Arg.var ld7, Arg.imm 1, ()) } fun pa =>
               Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                           args := (Arg.var pa.fst, Arg.imm 0, ()) } fun pb =>
               Expr.jnz (Arg.var pb.fst)
                 (Expr.jump Js_b.fst (Arg.imm 64, ())) (Expr.jump Js_b.fst (Arg.imm 32, ())))
            (Expr.jump Js ()))
        Blocks.nil)
    fun Js_lp => Expr.jump Js_lp.fst (Arg.imm 0, ())

private theorem commit_flag_loop_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {olen : BitVec 32} {Js : Cont []}
    {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hol_le : olen.toNat ≤ c.max_vars)
    (hlits : ∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (fl' : List (BitVec 32)) (m' : Mem 64),
      fl'.length = c.max_vars →
      (FullMem c { s with core := { s.core with flags := fl' } } ⋆ R) m' → Js () m') :
    wp Γ Q X (commitFlagLoopExpr c c.pFlags olen Js) m := by
  dsimp only [commitFlagLoopExpr]
  refine @wp_while_state1 Γ [i64] i32 Q X m _ _ (BitVec 32 × List (BitVec 32))
    Prod.fst (fun st => olen.toNat - st.1.toNat)
    (fun st mk => st.1.toNat ≤ olen.toNat ∧ st.2.length = c.max_vars ∧
      (FullMem c { s with core := { s.core with flags := st.2 } } ⋆ R) mk) ?_ ?_
  · intro J hJ
    viv_step
    exact hJ (0#32, s.core.flags) m ⟨Nat.zero_le _, hsp.1.core_ok.flags_len, hm⟩
  · intro J ⟨k, flk⟩ mk ⟨hle, hfl, hmk⟩ hrec
    dsimp only at hle hfl hmk
    dsimp only [Blocks.get]
    viv_step; viv_step
    · have hk_lt : k.toNat < olen.toNat := BitVec.lt_def.mp (by assumption)
      have hk_ws2 : (BitVec.setWidth 64 k).toNat < s.scratch.work_stk2.length := by
        have := hsp.1.scratch_ok.work_stk2_len; bv_omega
      have hk_idx : (BitVec.setWidth 64 k).toNat = k.toNat := by
        have := c.hmaxv; have hdb : dimacsBound = 2 ^ 28 := rfl; bv_omega
      viv_hfast_nogrp
      have hws2_k : k.toNat < s.scratch.work_stk2.length := by omega
      let lk := s.scratch.work_stk2[(BitVec.setWidth 64 k).toNat]'hk_ws2
      have hlk_lt : lk.toNat < 2 * s.core.cur_vars := by
        have := hlits k.toNat hk_lt
        rw [List.getElem?_eq_getElem hws2_k, Option.getD_some] at this
        simpa only [lk, hk_idx] using this
      have hcv : s.core.cur_vars ≤ c.max_vars := hsp.1.core_ok.cur_vars_le
      have hdb : dimacsBound = 2 ^ 28 := rfl; have := c.hmaxv
      have hv_lt : (BitVec.setWidth 64 (lk >>> 1#32)).toNat < flk.length := by
        rw [hfl, BitVec.toNat_setWidth, bv32_lshr1_toNat]; bv_omega
      refine wp_join_group (ts := [i32])
        (fun _ mb => (FullMem c { s with core := { s.core with flags := flk } } ⋆ R) mb) ?_ ?_
      · rintro _ ⟨bit, ⟨⟩⟩ mb hmb
        viv_hfast
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        let flk' := flk.set (BitVec.setWidth 64 (lk >>> 1#32)).toNat
          (((flk[(BitVec.setWidth 64 (lk >>> 1#32)).toNat]'hv_lt) ||| 8#32) ||| 16#32 ||| bit)
        exact hrec (k + 1#32, flk') _ (by dsimp only; omega)
          ⟨by dsimp only; omega, by dsimp only [flk']; rw [List.length_set, hfl], by assumption⟩
      · intro Jb hJb
        viv_hfast <;> exact hJb _ mk hmk
    · viv_hfast
      exact hk flk mk hfl hmk

private def commitPostShrinkExpr (c : FullCfg) (cref olen hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun p31 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p31.fst, Arg.imm 2, ()) }
    fun p32 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p32.fst, Arg.imm 4, ()) }
    fun p33 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.pArena, Arg.var p33.fst, ()) }
    fun p34 =>
  Expr.store (Arg.var olen) (Arg.var p34.fst)
    (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) } fun p35 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var p35.fst, Arg.imm 1, ()) }
      fun p36 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p36.fst, Arg.imm 4, ()) }
      fun p37 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pArena, Arg.var p37.fst, ()) } fun p38 =>
    Expr.store (t := i32) (Arg.imm 2) (Arg.var p38.fst)
      (Expr.group
        (fun Js =>
          Blocks.cons
            (fun (p39 : Tup Val [i32]) =>
              Expr.group
                (fun Js_sh =>
                  Blocks.cons
                    (fun (p40 : Tup Val [i32]) =>
                      Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                   args := (Arg.var cref, ()) } fun p41 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                   args := (Arg.var p41.fst, Arg.imm 4, ()) } fun p42 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                   args := (Arg.var c.pArena, Arg.var p42.fst, ()) } fun p43 =>
                      Expr.store (Arg.var p40.fst) (Arg.var p43.fst)
                        (Expr.group (fun Js_wp => Blocks.cons
                            (fun (_ : Tup Val []) => commitWatchPairExpr c cref) Blocks.nil)
                          fun Js_wp =>
                          Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                       args := (Arg.var p40.fst, Arg.imm 4194304, ()) } fun p44 =>
                          Expr.let_ { sig := [i32, i32],
                                       code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                                       args := (Arg.var p44.fst, Arg.imm 0, ()) } fun p45 =>
                          Expr.jnz (Arg.var p45.fst)
                            (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                         args := (Arg.var c.hdr, Arg.imm 800, ()) } fun p46 =>
                             Expr.load i64 (Arg.var p46.fst) fun ld =>
                             commitFlagLoopExpr c ld olen Js_wp.fst)
                            (Expr.jump Js_wp.fst ())))
                    Blocks.nil)
                fun Js_sh =>
                Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var p39.fst, Arg.imm 8388608, ()) } fun p40 =>
                Expr.let_ { sig := [i32, i32],
                            code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                            args := (Arg.var p40.fst, Arg.imm 0, ()) } fun p41 =>
                Expr.jnz (Arg.var p41.fst)
                  (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.var cref, ()) } fun pa =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var pa.fst, Arg.imm 3, ()) } fun pb =>
                   Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.var old_sz, ()) } fun p42 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var pb.fst, Arg.var p42.fst, ()) } fun pc =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.sub i64,
                               args := (Arg.var pc.fst, Arg.imm 1, ()) } fun pd =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var pd.fst, Arg.imm 4, ()) } fun pe =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var c.pArena, Arg.var pe.fst, ()) } fun pf =>
                   Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var pf.fst)
                     (Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                  args := (Arg.var p39.fst, Arg.imm 8388608, ()) } fun pg =>
                      Expr.jump Js_sh.fst (Arg.var pg.fst, ())))
                  (Expr.jump Js_sh.fst (Arg.var p39.fst, ())))
            Blocks.nil)
        fun Js_gl =>
        Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var hdr_v, Arg.imm 4194304, ()) } fun p39 =>
        Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                    args := (Arg.var p39.fst, Arg.imm 0, ()) } fun p40 =>
        Expr.jnz (Arg.var p40.fst)
          (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                       args := (Arg.var hdr_v, Arg.imm 524287, ()) } fun p41 =>
           Expr.group
             (fun Js_1 => Blocks.cons
               (fun (p : Tup Val [i32]) => Expr.jump Js_gl.fst (Arg.var p.fst, ())) Blocks.nil)
             fun Js_1 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                         args := (Arg.var p41.fst, Arg.var olen, ()) } fun p42 =>
             Expr.jnz (Arg.var p42.fst)
               (Expr.let_ { sig := [i32], code := OpCode.not i32, args := (Arg.imm 524287, ()) }
                  fun p43 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var hdr_v, Arg.var p43.fst, ()) } fun p44 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.sub i32,
                            args := (Arg.var olen, Arg.imm 1, ()) } fun p45 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var p45.fst, Arg.imm 524287, ()) } fun p46 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                            args := (Arg.var p44.fst, Arg.var p46.fst, ()) } fun p47 =>
                Expr.jump Js_1.fst (Arg.var p47.fst, ()))
               (Expr.jump Js_1.fst (Arg.var hdr_v, ())))
          (Expr.jump Js_gl.fst (Arg.var hdr_v, ()))))

private theorem commit_post_shrink_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s_uw : FullState}
    {R : Mem 64 → Prop} {m_cp : Mem 64} {ar_cp : List (BitVec 32)}
    {cref olen old_sz : BitVec 32} {Q : Post [i64]} {X : XPost}
    (hsp_uw : FullSparseInvW c F0 F_cur s_uw) (hpr_uw : VivCommitPres s0 s_uw)
    (href_uw : cref.toNat ∈ fullArenaClauseRefs s_uw)
    (hnonact : Spec.NonActiveReason s_uw.core cref.toNat)
    (hng_uw : fullArenaClauseGarb s_uw cref.toNat = false)
    (hsz_uw : fullArenaClauseSize s_uw cref.toNat = old_sz.toNat)
    (hol3 : 3 ≤ olen.toNat) (holt : olen.toNat < old_sz.toNat) (hol_mv : olen.toNat ≤ c.max_vars)
    (har_cp_len : ar_cp.length = c.arena_cap)
    (hout_cp : ∀ p, p < cref.toNat + 3 ∨ cref.toNat + 3 + olen.toNat ≤ p →
      ar_cp[p]? = s_uw.core.arena[p]?)
    (hmap_cp : ∀ t < olen.toNat, ar_cp[cref.toNat + 3 + t]? = s_uw.scratch.work_stk2[t]?)
    (hlits : ∀ i < olen.toNat,
      (s_uw.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s_uw.core.cur_vars)
    (hnd : ((s_uw.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s_uw.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hm_cp : (FullMem c { s_uw with core := { s_uw.core with arena := ar_cp } } ⋆ R) m_cp)
    (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitPostShrinkExpr c cref olen (fullArenaHdr s_uw cref.toNat) old_sz) m_cp := by
  have hbd_uw := viv_clause_bd hsp_uw href_uw
  have hsz_uw' : fullArenaClauseSizeCore s_uw.core cref.toNat = old_sz.toNat := hsz_uw
  have har_len_uw : s_uw.core.arena.length = c.arena_cap := hsp_uw.1.core_ok.arena_len_arr
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have harena_lt : c.arena_cap < 2 * 2 ^ 28 := hdb ▸ c.harena
  have hcp_bd : cref.toNat + 3 + old_sz.toNat ≤ ar_cp.length := by omega
  have hcref_lt : cref.toNat < 2147483648 := by omega
  have hc2_idx : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by simp; omega
  have hc1_idx : (BitVec.setWidth 64 cref + 1).toNat = cref.toNat + 1 := by simp; omega
  have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by simp; omega
  have hterm_idx : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 old_sz - 1).toNat =
      cref.toNat + 3 + old_sz.toNat - 1 := by simp; omega
  have hsz_prop := ar_set_sz_props (ar0 := ar_cp) (ar_orig := s_uw.core.arena)
    (cref := cref.toNat) (old_sz := old_sz.toNat) (nsz := olen.toNat) (nsz_bv := olen)
    (p2 := (BitVec.setWidth 64 cref + 2).toNat) (p1 := (BitVec.setWidth 64 cref + 1).toNat)
    (by omega) hol3 holt hcp_bd rfl hc2_idx hc1_idx hout_cp
  let ar_sz := (ar_cp.set (BitVec.setWidth 64 cref + 2).toNat olen).set
    (BitVec.setWidth 64 cref + 1).toNat 2#32
  dsimp only [commitPostShrinkExpr]
  viv_hfast_nogrp
  let hdr_v := fullArenaHdr s_uw cref.toNat
  have hng_hv : hdr_v &&& 524288#32 = 0#32 := by
    have : fullArenaClauseGarbCore s_uw.core cref.toNat = false := hng_uw
    unfold fullArenaClauseGarbCore at this; simpa [hdr_v, fullArenaHdr] using this

  refine wp_join_group (ts := [i32])
    (fun (nhdr, ()) m_gl => nhdr &&& 524288#32 = 0#32 ∧
      hdr_v &&& 8388608#32 = nhdr &&& 8388608#32 ∧
      (FullMem c { s_uw with core := { s_uw.core with arena := ar_sz } } ⋆ R) m_gl) ?_ ?_
  · rintro _ ⟨nhdr, ⟨⟩⟩ m_gl ⟨hng_nh, hsh_nh, hm_gl⟩
    refine wp_join_group (ts := [i32])
      (fun (nhdr', ()) m_sh => ∃ ar_pre : List (BitVec 32),
        ar_pre.length = c.arena_cap ∧
        let ar_sh := ar_pre.set cref.toNat nhdr'
        (∀ k, k < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ k →
          ar_sh[k]? = s_uw.core.arena[k]?) ∧
        ar_sh[cref.toNat]?.getD 0#32 &&& 524288#32 = 0#32 ∧
        ar_sh[cref.toNat]?.getD 0#32 &&& 8388608#32 ≠ 0#32 ∧
        (ar_sh[cref.toNat + 2]?.getD 0#32).toNat = olen.toNat ∧
        M6ShrkPad ar_sh s_uw.core.arena cref.toNat old_sz.toNat olen.toNat ∧
        (∀ t < olen.toNat, ar_sh[cref.toNat + 3 + t]? = ar_sz[cref.toNat + 3 + t]?) ∧
        (FullMem c { s_uw with core := { s_uw.core with arena := ar_pre } } ⋆ R) m_sh) ?_ ?_
    · rintro _ ⟨nhdr', ⟨⟩⟩ m_sh ⟨ar_pre, hal_pre, hout_sh, hng_sh, hsh_sh, hnsz_sh, hpad_sh,
          hcopy_sh, hm_pre⟩
      let ar_sh := ar_pre.set cref.toNat nhdr'
      have hal_sh : ar_sh.length = c.arena_cap := by rw [List.length_set, hal_pre]
      have hc0_pre : (BitVec.setWidth 64 cref).toNat < ar_pre.length := by omega
      viv_hfast_nogrp
      let s_sh : FullState := { s_uw with core := { s_uw.core with arena := ar_sh } }
      have hlits_sh : ∀ j < olen.toNat,
          (ar_sh[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s_uw.core.cur_vars := by
        intro j hj
        rw [hcopy_sh j hj, hsz_prop.2.2.2.1 j hj, hmap_cp j hj]
        exact hlits j hj
      have hws2_olen : olen.toNat ≤ s_uw.scratch.work_stk2.length := by
        have := hsp_uw.1.scratch_ok.work_stk2_len; omega
      have hmap_sh_eq : fullArenaClauseLitsCore s_sh.core cref.toNat =
          (s_uw.scratch.work_stk2.take olen.toNat).map BitVec.toNat := by
        refine fullArenaClauseLitsCore_eq_map_take (k := s_sh.core) (r := cref.toNat)
          (nsz := olen.toNat) (out := s_uw.scratch.work_stk2) hnsz_sh
          (by change cref.toNat + 3 + olen.toNat ≤ ar_sh.length; omega) hws2_olen
          fun j hj => by change ar_sh[cref.toNat + 3 + j]? = _; rw [hcopy_sh j hj,
            hsz_prop.2.2.2.1 j hj, hmap_cp j hj]
      have hnd_sh : (List.map (· / 2) (fullArenaClauseLitsCore s_sh.core cref.toNat)).Nodup := by
        rw [hmap_sh_eq, List.map_map]; simpa [Function.comp_def] using hnd
      have hent_sh : (cnfOfClauses F_cur).EntailsClause
          (cnfClause (fullArenaClauseLitsCore s_sh.core cref.toNat)) := by
        rw [hmap_sh_eq]; exact hent
      have hshrink := fullSparseInvW_of_inPlaceShrink_hnonact
        (ni' := s_uw.core.num_irred) (nr' := s_uw.core.num_redundant)
        hsp_uw href_uw hnonact hng_uw hol3 (hsz_uw.symm ▸ holt) hal_sh
        (hsz_uw.symm ▸ hout_sh) hng_sh hsh_sh hnsz_sh (hsz_uw.symm ▸ hpad_sh)
        hlits_sh hnd_sh hent_sh
      have hsp_sh : FullSparseInvW c F0 F_cur s_sh := hshrink.1
      have hrefs_sh : fullArenaClauseRefs s_sh = fullArenaClauseRefs s_uw := hshrink.2.1
      have href_sh : cref.toNat ∈ fullArenaClauseRefs s_sh := hrefs_sh ▸ href_uw
      have hpr_sh : VivCommitPres s0 s_sh :=
        hpr_uw.trans (VivCommitPres.of_refs rfl rfl rfl rfl hrefs_sh rfl rfl)
      refine wp_join0 (fun m_fl => ∃ s_fl, FullSparseInvW c F0 F_cur s_fl ∧
          VivCommitPres s0 s_fl ∧ cref.toNat ∈ fullArenaClauseRefs s_fl ∧
          s_fl.scratch.work_stk2 = s_uw.scratch.work_stk2 ∧ (FullMem c s_fl ⋆ R) m_fl) ?_ ?_
      · rintro _ m_fl ⟨s_fl, hsp_fl, hpr_fl, href_fl, hws2_fl, hm_fl⟩
        exact commit_watch_pair_wp Γ hBt hWpush hsp_fl hpr_fl href_fl hcref_lt (by omega) hm_fl hQ
      · intro J_wp hJ_wp
        viv_hfast_nogrp
        · viv_hfast_nogrp
          refine commit_flag_loop_wp (R := R) Γ hsp_sh hol_mv hlits ?_
            fun fl' m_fl hfl' hm_fl => ?_
          · dsimp only [s_sh, ar_sh]; rw [← hc0_idx]; assumption
          let s_fl : FullState := { s_sh with core := { s_sh.core with flags := fl' } }
          have hsp_fl : FullSparseInvW c F0 F_cur s_fl := viv_with_flags hsp_sh hfl'
          have hpr_fl : VivCommitPres s0 s_fl :=
            hpr_sh.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
          exact hJ_wp m_fl ⟨s_fl, hsp_fl, hpr_fl, href_sh, rfl, hm_fl⟩
        · refine hJ_wp _ ⟨s_sh, hsp_sh, hpr_sh, href_sh, rfl, ?_⟩
          dsimp only [s_sh, ar_sh]; rw [← hc0_idx]; assumption
    · intro J_sh hJ_sh
      viv_step; viv_step
      · have hsh0 : nhdr &&& 8388608#32 = 0#32 := by assumption
        have hterm_lt : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 old_sz - 1).toNat <
            ar_sz.length := by rw [hterm_idx, hsz_prop.1, har_len_uw]; omega
        viv_hfast
        let ar_t := ar_sz.set (cref.toNat + 3 + old_sz.toNat - 1) 4294967295#32
        have hsh_orig : s_uw.core.arena[cref.toNat]?.getD 0#32 &&& 8388608#32 =
            nhdr &&& 8388608#32 := by simpa [hdr_v, fullArenaHdr, fullArenaHdrCore] using hsh_nh
        have hf := ar_set_shrk_facts (ar_sz := ar_sz) (ar_orig := s_uw.core.arena)
          (cref := cref.toNat) (old_sz := old_sz.toNat) (nsz := olen.toNat)
          (term := cref.toNat + 3 + old_sz.toNat - 1) (nhdr := nhdr)
          (by rw [hsz_prop.1, har_len_uw]) (by omega) rfl holt hol3 hng_nh hsh0 hsh_orig
          hsz_prop.2.1 hsz_prop.2.2.1 hsz_prop.2.2.2.2.1
        have hne_ct : cref.toNat ≠ cref.toNat + 3 + old_sz.toNat - 1 := by omega
        have hcomm : ar_t.set cref.toNat (nhdr ||| 8388608#32) =
            (ar_sz.set cref.toNat (nhdr ||| 8388608#32)).set
              (cref.toNat + 3 + old_sz.toNat - 1) 4294967295#32 := by
          dsimp only [ar_t]; exact List.set_comm _ _ hne_ct.symm
        have hcopy_sh : ∀ t < olen.toNat,
            (ar_t.set cref.toNat (nhdr ||| 8388608#32))[cref.toNat + 3 + t]? =
              ar_sz[cref.toNat + 3 + t]? := fun t ht => by
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        refine hJ_sh (nhdr ||| 8388608#32, ()) _ ⟨ar_t, by rw [List.length_set, hsz_prop.1,
          har_len_uw], ?_, ?_, ?_, ?_, ?_, hcopy_sh, ?_⟩
        · simpa [hcomm] using hf.2.1
        · simpa [hcomm] using hf.2.2.1
        · simpa [hcomm] using hf.2.2.2.1
        · simpa [hcomm] using hf.2.2.2.2.1
        · simpa [hcomm] using hf.2.2.2.2.2
        · dsimp only [ar_t]; rw [← hterm_idx]; assumption
      · viv_hfast
        have hsh_ne0 : nhdr &&& 8388608#32 ≠ 0#32 := by assumption
        let ar_sh := ar_sz.set cref.toNat nhdr
        have hne_c2 : cref.toNat ≠ cref.toNat + 2 := by omega
        have hget0 : ar_sh[cref.toNat]? = some nhdr :=
          List.getElem?_set_self (by rw [hsz_prop.1, har_len_uw]; omega)
        have hout_sh : ∀ k, k < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ k →
            ar_sh[k]? = s_uw.core.arena[k]? := fun k hk => by
          dsimp only [ar_sh]
          rw [List.getElem?_set_ne (by omega)]
          exact hsz_prop.2.1 k hk
        have hng_sh : ar_sh[cref.toNat]?.getD 0#32 &&& 524288#32 = 0#32 := by
          rw [hget0, Option.getD_some]; exact hng_nh
        have hsh_sh : ar_sh[cref.toNat]?.getD 0#32 &&& 8388608#32 ≠ 0#32 := by
          rw [hget0, Option.getD_some]; exact hsh_ne0
        have hnsz_sh : (ar_sh[cref.toNat + 2]?.getD 0#32).toNat = olen.toNat := by
          dsimp only [ar_sh]; rw [List.getElem?_set_ne hne_c2]; exact hsz_prop.2.2.1
        have hpad_sh : M6ShrkPad ar_sh s_uw.core.arena cref.toNat old_sz.toNat olen.toNat := by
          unfold M6ShrkPad
          have hsh_orig : s_uw.core.arena[cref.toNat]?.getD 0#32 &&& 8388608#32 ≠ 0#32 := by
            have h1 : hdr_v &&& 8388608#32 =
                s_uw.core.arena[cref.toNat]?.getD 0#32 &&& 8388608#32 :=
              rfl
            rw [← h1, hsh_nh]; exact hsh_ne0
          simp only [hsh_orig, ↓reduceIte]
          intro k hk1 hk2
          dsimp only [ar_sh]
          rw [List.getElem?_set_ne (by omega)]
          exact hsz_prop.2.2.2.2.1 k hk1 hk2
        have hcopy_sh : ∀ t < olen.toNat, ar_sh[cref.toNat + 3 + t]? = ar_sz[cref.toNat + 3 + t]? :=
          fun t ht => List.getElem?_set_ne (by omega)
        exact hJ_sh (nhdr, ()) m_gl ⟨ar_sz, by rw [hsz_prop.1, har_len_uw], hout_sh, hng_sh,
          hsh_sh, hnsz_sh, hpad_sh, hcopy_sh, by simpa [ar_sz] using hm_gl⟩
  · intro J_gl hJ_gl
    viv_step; viv_step
    · viv_hfast
      · let gl := (olen - 1#32) &&& 524287#32
        have hgl_ng : gl &&& 524288#32 = 0#32 := bv32_glue_mask_garb _
        have hgl_nsh : gl &&& 8388608#32 = 0#32 := bv32_glue_mask_shrk _
        have hng' : ((hdr_v &&& ~~~524287#32) ||| gl) &&& 524288#32 = 0#32 := by
          rw [bv32_set_glue_garb _ _ hgl_ng]; exact hng_hv
        have hsh' : hdr_v &&& 8388608#32 =
            ((hdr_v &&& ~~~524287#32) ||| gl) &&& 8388608#32 :=
          (bv32_set_glue_shrk _ _ hgl_nsh).symm
        refine hJ_gl (_, ()) _ ⟨hng', hsh', ?_⟩
        dsimp only [ar_sz]; assumption
      · refine hJ_gl (hdr_v, ()) _ ⟨hng_hv, rfl, ?_⟩
        dsimp only [ar_sz]; assumption
    · viv_hfast
      refine hJ_gl (hdr_v, ()) _ ⟨hng_hv, rfl, ?_⟩
      dsimp only [ar_sz]; assumption

private def commitCopyLoopExpr (c : FullCfg) (cref olen hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (p29 : Tup Val [i32]) =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                      args := (Arg.var p29.fst, Arg.var olen, ()) } fun p30 =>
          Expr.jnz (Arg.var p30.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
               fun pa =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var pa.fst, Arg.imm 3, ()) } fun pb =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p29.fst, ()) }
               fun p31 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var pb.fst, Arg.var p31.fst, ()) } fun pc =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var pc.fst, Arg.imm 4, ()) } fun pd =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pArena, Arg.var pd.fst, ()) } fun pe =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p29.fst, ()) }
               fun p32 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p32.fst, Arg.imm 4, ()) } fun p33 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk2, Arg.var p33.fst, ()) } fun p34 =>
             Expr.load i32 (Arg.var p34.fst) fun ld =>
             Expr.store (Arg.var ld) (Arg.var pe.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p29.fst, Arg.imm 1, ()) } fun pn =>
                Expr.jump Js.fst (Arg.var pn.fst, ())))
            (commitPostShrinkExpr c cref olen hdr_v old_sz))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem commit_copy_loop_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s_uw : FullState}
    {R : Mem 64 → Prop} {m_uw : Mem 64} {cref olen old_sz : BitVec 32}
    {Q : Post [i64]} {X : XPost}
    (hsp_uw : FullSparseInvW c F0 F_cur s_uw) (hpr_uw : VivCommitPres s0 s_uw)
    (href_uw : cref.toNat ∈ fullArenaClauseRefs s_uw)
    (hnonact : Spec.NonActiveReason s_uw.core cref.toNat)
    (hng_uw : fullArenaClauseGarb s_uw cref.toNat = false)
    (hsz_uw : fullArenaClauseSize s_uw cref.toNat = old_sz.toNat)
    (hol3 : 3 ≤ olen.toNat) (holt : olen.toNat < old_sz.toNat) (hol_mv : olen.toNat ≤ c.max_vars)
    (hlits : ∀ i < olen.toNat,
      (s_uw.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s_uw.core.cur_vars)
    (hnd : ((s_uw.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s_uw.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hm_uw : (FullMem c s_uw ⋆ R) m_uw) (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitCopyLoopExpr c cref olen (fullArenaHdr s_uw cref.toNat) old_sz) m_uw := by
  have hbd_uw := viv_clause_bd hsp_uw href_uw
  have hsz_uw' : fullArenaClauseSizeCore s_uw.core cref.toNat = old_sz.toNat := hsz_uw
  have har_len : s_uw.core.arena.length = c.arena_cap := hsp_uw.1.core_ok.arena_len_arr
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have harena_lt : c.arena_cap < 2 * 2 ^ 28 := hdb ▸ c.harena
  dsimp only [commitCopyLoopExpr]
  refine @wp_while_state1 Γ [i64] i32 Q X m_uw _ _ (BitVec 32 × List (BitVec 32))
    Prod.fst (fun st => olen.toNat - st.1.toNat)
    (fun st mi => st.1.toNat ≤ olen.toNat ∧ st.2.length = c.arena_cap ∧
      (∀ p, p < cref.toNat + 3 ∨ cref.toNat + 3 + olen.toNat ≤ p →
        st.2[p]? = s_uw.core.arena[p]?) ∧
      (∀ t < st.1.toNat, st.2[cref.toNat + 3 + t]? = s_uw.scratch.work_stk2[t]?) ∧
      (FullMem c { s_uw with core := { s_uw.core with arena := st.2 } } ⋆ R) mi) ?_ ?_
  · intro J hJ
    viv_step
    exact hJ (0#32, s_uw.core.arena) m_uw ⟨Nat.zero_le _, har_len, fun _ _ => rfl,
      fun _ h => absurd h (Nat.not_lt_zero _), hm_uw⟩
  · intro J ⟨i, ari⟩ mi ⟨hle, hlen, hout, hmap, hmi⟩ hrec
    dsimp only at hle hlen hout hmap
    dsimp only [Blocks.get]
    viv_step; viv_step
    · have hi_lt : i.toNat < olen.toNat := BitVec.lt_def.mp (by assumption)
      have hi_ws2 : (BitVec.setWidth 64 i).toNat < s_uw.scratch.work_stk2.length := by
        have := hsp_uw.1.scratch_ok.work_stk2_len; bv_omega
      have hi_ar : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 i).toNat < ari.length := by
        rw [hlen]; bv_omega
      have hidx_ar : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 i).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hidx_ws2 : (BitVec.setWidth 64 i).toNat = i.toNat := by bv_omega
      viv_hfast
      let ari' := ari.set (cref.toNat + 3 + i.toNat)
        (s_uw.scratch.work_stk2[i.toNat]?.getD 0#32)
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hn_le : (i + 1#32).toNat ≤ olen.toNat := by omega
      have hout' : ∀ p, p < cref.toNat + 3 ∨ cref.toNat + 3 + olen.toNat ≤ p →
          ari'[p]? = s_uw.core.arena[p]? := fun p hp => by
        dsimp only [ari']; rw [List.getElem?_set_ne (by omega)]; exact hout p hp
      have hmap' : ∀ t < (i + 1#32).toNat, ari'[cref.toNat + 3 + t]? =
          s_uw.scratch.work_stk2[t]? := fun t ht => by
        dsimp only [ari']
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (hi1 ▸ ht)) with hlt_t | rfl
        · rw [List.getElem?_set_ne (by omega)]; exact hmap t hlt_t
        · rw [List.getElem?_set_self (by omega)]
          have := hsp_uw.1.scratch_ok.work_stk2_len
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      refine hrec (i + 1#32, ari') _ (by dsimp only; omega)
        ⟨hn_le, by rw [List.length_set, hlen], hout', hmap', ?_⟩
      have hi_w := hsp_uw.1.scratch_ok.work_stk2_len
      have hval_eq : s_uw.scratch.work_stk2[i.toNat]?.getD 0#32 =
          s_uw.scratch.work_stk2[(BitVec.setWidth 64 i).toNat]'hi_ws2 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hidx_ws2]
      dsimp only [ari']
      rw [← hidx_ar, hval_eq]
      exact (by assumption)
    · have hnlt : ¬ i.toNat < olen.toNat := fun h =>
        (by assumption : ¬ i < olen) (BitVec.lt_def.mpr h)
      have hi_eq : i.toNat = olen.toNat := by omega
      exact commit_post_shrink_wp Γ hBt hWpush hsp_uw hpr_uw href_uw hnonact hng_uw hsz_uw
        hol3 holt hol_mv hlen hout (fun t ht => hmap t (hi_eq ▸ ht)) hlits hnd hent hmi hQ

private def commitNszGe3Expr (c : FullCfg) (cref olen implied hdr_v old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun (_ : Tup Val []) =>
          Expr.call (as := [i64, i32]) (bs := []) "full_viv_unreason_m6"
            (Arg.var c.hdr, Arg.var cref, ()) fun _ =>
          Expr.call (as := [i64, i32]) (bs := []) "full_viv_best_watch_m6"
            (Arg.var c.hdr, Arg.var olen, ()) fun _ =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
            fun p19 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p19.fst, Arg.imm 3, ()) } fun p20 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p20.fst, Arg.imm 4, ()) } fun p21 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p21.fst, ()) } fun p22 =>
          Expr.load i32 (Arg.var p22.fst) fun ld5 =>
          Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
            (Arg.var c.hdr, Arg.var ld5, Arg.var cref, ()) fun _ =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cref, ()) }
            fun p24 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p24.fst, Arg.imm 4, ()) } fun p25 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p25.fst, Arg.imm 4, ()) } fun p26 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p26.fst, ()) } fun p27 =>
          Expr.load i32 (Arg.var p27.fst) fun ld6 =>
          Expr.call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
            (Arg.var c.hdr, Arg.var ld6, Arg.var cref, ()) fun _ =>
          commitCopyLoopExpr c cref olen hdr_v old_sz)
        Blocks.nil)
    fun Js =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                args := (Arg.var implied, Arg.imm 4294967295, ()) } fun p16 =>
    Expr.jnz (Arg.var p16.fst)
      (Expr.let_ { sig := [i32, i32], code := OpCode.sub i32,
                   args := (Arg.var olen, Arg.imm 2, ()) } fun p17 =>
       Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p17.fst, ()) }
         fun p18 =>
       Expr.group (fun Js1 => Blocks.cons (fun (_ : Tup Val []) => Expr.jump Js.fst ()) Blocks.nil)
         fun Js1 => commitBacktrackGtExpr c.hdr p18.fst Js1.fst)
      (Expr.jump Js.fst ())

private theorem commit_nsz_ge3_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    (hUnreason : Γ.Has "full_viv_unreason_m6" fullVivUnreasonM6Spec)
    (hBestW : Γ.Has "full_viv_best_watch_m6" fullVivBestWatchM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s1 : FullState}
    {R : Mem 64 → Prop} {m1 : Mem 64} {cref olen implied old_sz : BitVec 32}
    {Q : Post [i64]} {X : XPost}
    (hsp1 : FullSparseInvW c F0 F_cur s1) (hpr1 : VivCommitPres s0 s1)
    (har1 : s1.core.arena = s0.core.arena) (hws2_1 : s1.scratch.work_stk2 = s0.scratch.work_stk2)
    (href : cref.toNat ∈ fullArenaClauseRefs s0)
    (_hng : fullArenaClauseGarb s0 cref.toNat = false)
    (hsz : fullArenaClauseSize s0 cref.toNat = old_sz.toNat)
    (hol3 : 3 ≤ olen.toNat) (holt : olen.toNat < old_sz.toNat) (hol_mv : olen.toNat ≤ c.max_vars)
    (hlits : ∀ i < olen.toNat, (s0.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hnd : ((s0.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s0.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : VivCommitQ c F0 F_cur s0 R Q) :
    wp Γ Q X (commitNszGe3Expr c cref olen implied (fullArenaHdr s0 cref.toNat) old_sz) m1 := by
  dsimp only [commitNszGe3Expr]
  viv_to_group
  refine wp_join0 (fun m2 => ∃ s2, FullSparseInvW c F0 F_cur s2 ∧ VivCommitPres s0 s2 ∧
      s2.core.arena = s0.core.arena ∧ s2.scratch.work_stk2 = s0.scratch.work_stk2 ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro _ m2 ⟨s2, hsp2, hpr2, har2, hws2_2, hm2⟩
    viv_call hUnreason
    refine ⟨c, F0, F_cur, s2, R, rfl, hsp2, hm2, ?_⟩
    intro su mu hsp_u hnonact hcv_u har_u hal_u hpr_u hfu_u _ hws2_u hrr_u htr_u _ _ hmu
    have hrefs_u_eq : fullArenaClauseRefs su = fullArenaClauseRefs s2 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har_u, hal_u]
    have href_u : cref.toNat ∈ fullArenaClauseRefs su := by
      rw [hrefs_u_eq, hpr2.2.2.2.2.1]; exact href
    have hpr_u' : VivCommitPres s0 su :=
      hpr2.trans (VivCommitPres.of_refs hcv_u hal_u hpr_u hfu_u hrefs_u_eq hrr_u htr_u)
    viv_call hBestW
    have hlits_u : ∀ i < olen.toNat,
        (su.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * su.core.cur_vars := by
      intro i hi; rw [hcv_u, hws2_u, hws2_2, hpr2.1]; exact hlits i hi
    refine ⟨c, su, R, rfl, hsp_u.1, hol_mv, hlits_u, hmu, ?_⟩
    intro ws2' mbw hws2'_len hperm hmbw
    let sbw : FullState := { su with scratch := { su.scratch with work_stk2 := ws2' } }
    have hsp_bw : FullSparseInvW c F0 F_cur sbw := viv_with_ws2 hsp_u hws2'_len
    have hpr_bw : VivCommitPres s0 sbw :=
      hpr_u'.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    have href_bw : cref.toNat ∈ fullArenaClauseRefs sbw := href_u
    have hbd_bw := viv_clause_bd hsp_bw href_bw
    have hsz_bw : fullArenaClauseSizeCore sbw.core cref.toNat = old_sz.toNat := by
      unfold fullArenaClauseSizeCore
      rw [show sbw.core.arena = s0.core.arena from har_u.trans har2]; exact hsz
    have hdb : dimacsBound = 2 ^ 28 := rfl
    have harena_lt : c.arena_cap < 2 * 2 ^ 28 := hdb ▸ c.harena
    have har_bw_len : sbw.core.arena.length = c.arena_cap := hsp_bw.1.core_ok.arena_len_arr
    have hc3_lt : (BitVec.setWidth 64 cref + 3).toNat < sbw.core.arena.length := by bv_omega
    have hc4_lt : (BitVec.setWidth 64 cref + 4).toNat < sbw.core.arena.length := by bv_omega
    viv_hfast_nogrp
    refine viv_unwatch_one_wp Γ hUnwatch hsp_bw hmbw fun wv1 ws1 wu1 m_u1 hsp_u1 hm_u1 => ?_
    let su1 : FullState :=
      { sbw with core := { sbw.core with wvec := wv1, wstk := ws1, wusable := wu1 } }
    viv_hfast_nogrp
    refine viv_unwatch_one_wp Γ hUnwatch hsp_u1 hm_u1 fun wv2 ws2 wu2 m_uw hsp_uw hm_uw => ?_
    let s_uw : FullState :=
      { su1 with core := { su1.core with wvec := wv2, wstk := ws2, wusable := wu2 } }
    have href_uw : cref.toNat ∈ fullArenaClauseRefs s_uw := href_u
    have hpr_uw : VivCommitPres s0 s_uw :=
      hpr_bw.trans (VivCommitPres.of_refs rfl rfl rfl rfl rfl rfl rfl)
    have hnonact_uw : Spec.NonActiveReason s_uw.core cref.toNat := hnonact
    have har_uw_eq : s_uw.core.arena = s0.core.arena := by
      change sbw.core.arena = _; exact har_u.trans har2
    have hng_uw : fullArenaClauseGarb s_uw cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [har_uw_eq]; exact _hng
    have hsz_uw : fullArenaClauseSize s_uw cref.toNat = old_sz.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [har_uw_eq]; exact hsz
    have hhdr_eq : fullArenaHdr s_uw cref.toNat = fullArenaHdr s0 cref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; rw [har_uw_eq]
    have hperm' : (ws2'.take olen.toNat).Perm (s0.scratch.work_stk2.take olen.toNat) := by
      simpa [hws2_u, hws2_2] using hperm
    have hlits_uw : ∀ i < olen.toNat,
        (s_uw.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s_uw.core.cur_vars := by
      intro i hi
      change (ws2'[i]?.getD 0#32).toNat < 2 * s_uw.core.cur_vars
      have hi_mem : ws2'[i]'(by rw [hws2'_len]; omega) ∈ ws2'.take olen.toNat := by
        refine List.mem_iff_getElem.mpr ⟨i, by rw [List.length_take, hws2'_len]; omega, ?_⟩
        simp
      have hi_mem0 : ws2'[i]'(by rw [hws2'_len]; omega) ∈ s0.scratch.work_stk2.take olen.toNat :=
        hperm'.mem_iff.mp hi_mem
      obtain ⟨j, hj_len, hj_eq⟩ := List.mem_iff_getElem.mp hi_mem0
      have hj_lt : j < olen.toNat := by rw [List.length_take] at hj_len; omega
      have hw0_len := hsp1.1.scratch_ok.work_stk2_len; rw [hws2_1] at hw0_len
      rw [List.getElem_take] at hj_eq
      rw [List.getElem?_eq_getElem (by rw [hws2'_len]; omega), Option.getD_some, ← hj_eq]
      have hl0 := hlits j hj_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hl0
      have hcv0 : s_uw.core.cur_vars = s0.core.cur_vars := hpr_uw.1
      omega
    have hnd_uw : ((s_uw.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup := by
      have hnd0 : ((s0.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup := hnd
      exact (hperm'.map _).nodup_iff.mpr hnd0
    have hent_uw : (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s_uw.scratch.work_stk2.take olen.toNat).map BitVec.toNat)) :=
      viv_entails_of_perm (hperm'.map BitVec.toNat) hent
    rw [← hhdr_eq]
    exact commit_copy_loop_wp Γ hBt hWpush hsp_uw hpr_uw href_uw hnonact_uw hng_uw hsz_uw
      hol3 holt hol_mv hlits_uw hnd_uw hent_uw hm_uw hQ
  · intro J hJ
    viv_hfast_nogrp
    · have hdb : dimacsBound = 2 ^ 28 := rfl
      have hmv_lt : c.max_vars < 2 * 2 ^ 28 := hdb ▸ c.hmaxv
      have hnl_mv : (BitVec.setWidth 64 (olen - 2#32)).toNat < c.max_vars := by bv_omega
      refine wp_join0 (fun m2 => ∃ s2, FullSparseInvW c F0 F_cur s2 ∧ VivCommitPres s0 s2 ∧
          s2.core.arena = s0.core.arena ∧ s2.scratch.work_stk2 = s0.scratch.work_stk2 ∧
          (FullMem c s2 ⋆ R) m2)
        (fun _ m2 h => by dsimp only [Blocks.get]; viv_hfast; exact hJ m2 h) ?_
      intro J1 hJ1
      exact commit_backtrack_gt_wp Γ hBt hsp1 hnl_mv hm1
        fun s2 m2 hsp2 hpr2 har2 hws2 hm2 =>
        hJ1 m2 ⟨s2, hsp2, hpr1.trans hpr2, har2.trans har1, hws2.trans hws2_1, hm2⟩
    · exact hJ m1 ⟨s1, hsp1, hpr1, har1, hws2_1, hm1⟩

end

/-! ## 4. Top-level `full_viv_commit_m6_wp` theorem -/

public theorem full_viv_commit_m6_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hBin : Γ.Has "full_add_bin_m6" fullAddBinSpec)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    (hUnreason : Γ.Has "full_viv_unreason_m6" fullVivUnreasonM6Spec)
    (hBestW : Γ.Has "full_viv_best_watch_m6" fullVivBestWatchM6Spec) :
    ∀ args m Q X, fullVivCommitM6Spec args m Q X →
      Func.wp Γ full_viv_commit_m6_body args m Q X := by
  rintro ⟨h, cref, olen, implied, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s0, R, rfl, hsp0, href0, hng0, hol_mv, hent_pre, hm0, hQ0⟩
  have hQ : VivCommitQ c F0 F_cur s0 R Q := fun r s' m' hsp' hpr' hr huns hm' =>
    hQ0 r s' m' hsp' hpr'.1 hpr'.2.1 hpr'.2.2.1 hpr'.2.2.2.1 hpr'.2.2.2.2.1
      hpr'.2.2.2.2.2.1 hpr'.2.2.2.2.2.2 hr huns hm'
  have hbd0 := viv_clause_bd hsp0 href0
  have har0_len := hsp0.1.core_ok.arena_len_arr
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have harena_lt : c.arena_cap < 2 * 2 ^ 28 := hdb ▸ c.harena
  have hc0_lt : (BitVec.setWidth 64 cref).toNat < s0.core.arena.length := by simp; omega
  have hc2_lt : (BitVec.setWidth 64 cref + 2).toNat < s0.core.arena.length := by simp; omega
  have hsz_eq : (s0.core.arena[(BitVec.setWidth 64 cref + 2).toNat]?.getD 0#32).toNat =
      fullArenaClauseSize s0 cref.toNat := by
    have h2 : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by simp; omega
    rw [h2]; rfl
  unfold Func.wp full_viv_commit_m6_body
  have hc2_idx : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by bv_omega
  have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
  have hsz_mod : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
  have hsz_toNat : ∀ hlt,
      (s0.core.arena[(BitVec.setWidth 64 cref + 2).toNat]'hlt).toNat =
      fullArenaClauseSize s0 cref.toNat := fun hlt => by
    rw [← hsz_eq, List.getElem?_eq_getElem hlt, Option.getD_some]
  have hsz_mod_toNat : ∀ hlt,
      (s0.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hlt).toNat =
      fullArenaClauseSize s0 cref.toNat := fun hlt => by
    have h := List.getElem?_eq_getElem hlt
    conv at h => lhs; rw [hsz_mod]
    have h' := congrArg (fun x : Option (BitVec 32) => (x.getD 0#32).toNat) h
    simpa [fullArenaClauseSize, fullArenaClauseSizeCore] using h'.symm
  have hhdr0_sw : ∀ hlt,
      s0.core.arena[(BitVec.setWidth 64 cref).toNat]'hlt = fullArenaHdr s0 cref.toNat :=
    fun hlt => by
      unfold fullArenaHdr fullArenaHdrCore
      rw [← hc0_idx, List.getElem?_eq_getElem hlt, Option.getD_some]
  let s1 : FullState :=
    { s0 with scratch := { s0.scratch with viv_cnt := s0.scratch.viv_cnt + 1#64 } }
  have hlen1 : s1.LengthsOk c := ⟨hsp0.1.core_ok, { hsp0.1.scratch_ok with }⟩
  have hsp1 : FullSparseInvW c F0 F_cur s1 :=
    commit_sparseW_of_core_pres hsp0 hlen1 hsp0.2.1 rfl rfl rfl rfl rfl rfl rfl
  have hpr1 : VivCommitPres s0 s1 := VivCommitPres.refl s0
  viv_hfast_nogrp
  · exact hQ 1#64 s0 m hsp0 (VivCommitPres.refl s0) (Or.inl rfl) (fun h => by cases h) hm0
  all_goals
    have hol_lt : olen.toNat < fullArenaClauseSize s0 cref.toNat := by
      have hge : ¬ (s0.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          rw [hsz_mod]; omega)).toNat ≤ olen.toNat := by assumption
      rw [hsz_mod_toNat] at hge
      omega
    obtain ⟨hlits, hnd, hent⟩ := hent_pre hol_lt
  · have hol0 : olen = 0#32 := by assumption
    have hent0 : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by
      simpa [hol0] using hent
    exact commit_nsz0_wp Γ hBt hsp1 hent0 (by assumption) hQ
  · have hne0 : olen ≠ 0#32 := by assumption
    have hle2 : olen.toNat ≤ 2 := BitVec.le_def.mp (by assumption)
    simp only [hhdr0_sw]
    exact commit_nsz12_wp Γ hBt hUnwatch hUnit hBin hsp1 hpr1 rfl rfl href0 hng0
      (hsz_toNat _).symm hne0 hle2 hol_mv ((hsz_toNat _).symm ▸ hol_lt)
      hlits hent (by assumption) hQ
  · have hne0 : olen ≠ 0#32 := by assumption
    have hnle : ¬ olen.toNat ≤ 2 := fun h => (by assumption : ¬ olen ≤ 2#32) (BitVec.le_def.mpr h)
    have hnz : olen.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq (by simpa using h))
    have hol3 : 3 ≤ olen.toNat := by omega
    simp only [hhdr0_sw]
    exact commit_nsz_ge3_wp Γ hBt hUnwatch hWpush hUnreason hBestW hsp1 hpr1 rfl rfl href0 hng0
      (hsz_toNat _).symm hol3 ((hsz_toNat _).symm ▸ hol_lt)
      hol_mv hlits hnd hent (by assumption) hQ

end LeanQbe.T.Examples.Kissat.Proof.Vivify
