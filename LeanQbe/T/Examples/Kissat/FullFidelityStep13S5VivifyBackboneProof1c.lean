/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S5-B — Vivify Finish (`Proof1c`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for
`FullFidelityStep13S5VivifyBackbone.full_viv_finish_m6_body` against canonical
`FullM6VivBackbone.fullVivFinishM6Spec` (factoring out the `FL_SUBSUME | FL_ELIM_C | FL_FACT_*`
promotion flag loop `s13_finish_flag_loop_wp` so every theorem stays `<= 420` lines).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullM6VivBackbone FullVivifyHelpers
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Promotion Subsumer Flag-Mark Loop (`L375-383`) -/

section FinishProof

private theorem s13_vivTmp_mem_of_perm {tmp : List (BitVec 32)} {sz : Nat} {lits : List Nat}
    (hsz : sz ≤ tmp.length) (hp : ((tmp.take sz).map BitVec.toNat).Perm lits) :
    ∀ k < sz, (tmp[k]?.getD 0#32).toNat ∈ lits := fun k hk => by
  rw [← hp.mem_iff, List.mem_map]
  have hk_t : k < (tmp.take sz).length := by simp [List.length_take, Nat.min_eq_left hsz]; omega
  refine ⟨tmp[k]'(by omega), ?_, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  simpa [List.getElem_take] using List.getElem_mem hk_t

private theorem s13_conflictOkW_to_viv {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) : FullVivifySpecs.FullVivConflictOk F_cur s := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | h2
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr h2

private theorem s13_sparseInvW_with_ant_res {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (asz rsz : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := asz, res_sz := rsz } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

private theorem s13_bv32_lshr1_fin (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]

private abbrev s13FinishFlagLoopExpr (c : FullCfg) (sub_ref : Val i64) (ssz_p : Val i32)
    (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun Jkp => Blocks.cons (fun (pk : Tup Val [i32]) =>
    fvOp (OpCode.cmp .ult i32 .bool rfl) (Arg.var pk.fst, Arg.var ssz_p, ()) fun ck =>
    Expr.jnz (Arg.var ck.fst)
      (fvOp (OpCode.add i64) (Arg.var sub_ref, Arg.imm 3, ()) fun p3 =>
       fvOp (OpCode.zext 32 64) (Arg.var pk.fst, ()) fun k64 =>
       fvOp (OpCode.add i64) (Arg.var p3.fst, Arg.var k64.fst, ()) fun pk3 =>
       fvOp (OpCode.mul i64) (Arg.var pk3.fst, Arg.imm 4, ()) fun ok3 =>
       fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var ok3.fst, ()) fun pak =>
       Expr.load i32 (Arg.var pak.fst) fun lp =>
       Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (pfb : Tup Val [i32]) =>
         fvOp (OpCode.lshr i32) (Arg.var lp, Arg.imm 1, ()) fun lph =>
         fvOp (OpCode.zext 32 64) (Arg.var lph.fst, ()) fun lph64 =>
         fvOp (OpCode.mul i64) (Arg.var lph64.fst, Arg.imm 4, ()) fun ofp =>
         fvOp (OpCode.add i64) (Arg.var c.pFlags, Arg.var ofp.fst, ()) fun pfp =>
         fvOp (OpCode.lshr i32) (Arg.var lp, Arg.imm 1, ()) fun lph2 =>
         fvOp (OpCode.zext 32 64) (Arg.var lph2.fst, ()) fun lph64b =>
         fvOp (OpCode.mul i64) (Arg.var lph64b.fst, Arg.imm 4, ()) fun ofpb =>
         fvOp (OpCode.add i64) (Arg.var c.pFlags, Arg.var ofpb.fst, ()) fun pfpb =>
         Expr.load i32 (Arg.var pfpb.fst) fun fl_old =>
         fvOp (OpCode.or i32) (Arg.var fl_old, Arg.imm 8, ()) fun fl1 =>
         fvOp (OpCode.or i32) (Arg.var fl1.fst, Arg.imm 16, ()) fun fl2 =>
         fvOp (OpCode.or i32) (Arg.var fl2.fst, Arg.var pfb.fst, ()) fun fl3 =>
         Expr.store (Arg.var fl3.fst) (Arg.var pfp.fst)
           (fvOp (OpCode.add i32) (Arg.var pk.fst, Arg.imm 1, ()) fun pk1 =>
            Expr.jump Jkp.fst (Arg.var pk1.fst, ()))) Blocks.nil) fun Jfp =>
       fvOp (OpCode.and i32) (Arg.var lp, Arg.imm 1, ()) fun lp1 =>
       fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var lp1.fst, Arg.imm 0, ()) fun clp1 =>
       Expr.jnz (Arg.var clp1.fst) (Expr.jump Jfp.fst (Arg.imm 64, ()))
         (Expr.jump Jfp.fst (Arg.imm 32, ())))
      k) Blocks.nil) fun Jkp => Expr.jump Jkp.fst (Arg.imm 0, ())

private theorem s13_finish_flag_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {sp : FullState} {R : Mem 64 → Prop}
    {sub_ref : Val i64} {ssz_p : Val i32} {k : Expr Val Cont [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur sp)
    (href : sub_ref.toNat ∈ fullArenaClauseRefs sp)
    (hng : fullArenaClauseGarb sp sub_ref.toNat = false)
    (hssz : ssz_p.toNat = fullArenaClauseSize sp sub_ref.toNat)
    (hm : (FullMem c sp ⋆ R) m)
    (hk : ∀ (fl' : List (BitVec 32)) m', fl'.length = c.max_vars →
      (FullMem c { sp with core := { sp.core with flags := fl' } } ⋆ R) m' →
      wp Γ Q X k m') :
    wp Γ Q X (s13FinishFlagLoopExpr c sub_ref ssz_p k) m := by
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have hcv := hcl.cur_vars_le
  have hmx := c.hmaxv; have hcap := c.harena; unfold dimacsBound at hmx hcap
  have hwf := hw.arena.refs_wf sub_ref.toNat href
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hbd : sub_ref.toNat + 3 + fullArenaClauseSizeCore sp.core sub_ref.toNat ≤
      sp.core.arena.length := by omega
  dsimp only [s13FinishFlagLoopExpr, fvOp]
  refine wp_loop_inv (ts := [i32])
    (fun (kp, ()) mk => kp.toNat ≤ ssz_p.toNat ∧ ∃ fl_k : List (BitVec 32),
      fl_k.length = c.max_vars ∧
      (FullMem c { sp with core := { sp.core with flags := fl_k } } ⋆ R) mk)
    (fun (kp, ()) _ => ssz_p.toNat - kp.toNat)
    (fun Jkp hJkp => by
      fvt_steps
      exact hJkp (0#32, ()) m ⟨Nat.zero_le _, sp.core.flags, hcl.flags_len, hm⟩)
    (fun Jkp (kp, ()) mk ⟨hkp_le, fl_k, hfl_k, hmk⟩ ihk => ?_)
  fvt_step; fvt_step
  · have hkp_lt : kp.toNat < ssz_p.toNat := by c0_bound
    have hkp1 : (kp + 1#32).toNat = kp.toNat + 1 := by bv_omega
    have hk_sz : kp.toNat < fullArenaClauseSizeCore sp.core sub_ref.toNat := by
      unfold fullArenaClauseSize at hssz; exact hssz ▸ hkp_lt
    have hk_idx : (sub_ref + 3#64 + kp.setWidth 64).toNat = sub_ref.toNat + 3 + kp.toNat := by
      bv_omega
    have hk_ar : (sub_ref + 3#64 + kp.setWidth 64).toNat < sp.core.arena.length := by omega
    let lp := sp.core.arena[(sub_ref + 3#64 + kp.setWidth 64).toNat]'hk_ar
    have hlp_eq : sp.core.arena[sub_ref.toNat + 3 + kp.toNat]'(by omega) = lp := by
      dsimp only [lp]; simp only [hk_idx]
    have hlp_mem : lp.toNat ∈ fullArenaClauseLits sp sub_ref.toNat :=
      (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨kp.toNat, hk_sz, congrArg BitVec.toNat hlp_eq⟩
    have hlp_lt : lp.toNat < 2 * sp.core.cur_vars :=
      hw.arena.lits_lt sub_ref.toNat href hng lp.toNat hlp_mem
    have hlp_fl : ((lp >>> 1#32).setWidth 64).toNat < fl_k.length := by
      have hshr : (lp >>> 1#32).toNat = lp.toNat / 2 := s13_bv32_lshr1_fin lp
      rw [hfl_k, BitVec.toNat_setWidth, hshr, Nat.mod_eq_of_lt (by omega)]; omega
    fvt_steps
    all_goals (
      refine ihk (kp + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
      rw [List.length_set, hfl_k])
  · fvt_steps
    exact hk fl_k mk hfl_k hmk

private theorem s13_finish_promote_irred_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sd : FullState} {shdr : BitVec 32} (hspd : FullSparseInvW c F0 F_cur sd)
    (hsub_ref : sd.scratch.ant_sz.toNat ∈ fullArenaClauseRefs sd)
    (hsub_ng : fullArenaClauseGarb sd sd.scratch.ant_sz.toNat = false)
    (hshdr_eq : fullArenaHdr sd sd.scratch.ant_sz.toNat = shdr)
    (h2_lt_s : sd.scratch.ant_sz.toNat + 2 < sd.core.arena.length)
    (nr' : BitVec 64) :
    let shdr' := shdr &&& ~~~0x00400000#32
    let sp : FullState :=
      { sd with
        core :=
          { sd.core with
            arena := sd.core.arena.set sd.scratch.ant_sz.toNat shdr'
            num_irred := sd.core.num_irred + 1#64
            num_redundant := nr' } }
    FullSparseInvW c F0 F_cur sp ∧
    fullArenaClauseRefs sp = fullArenaClauseRefs sd ∧
    fullArenaClauseGarb sp sd.scratch.ant_sz.toNat = false ∧
    (sd.core.arena[(sd.scratch.ant_sz + 2).toNat]'(by
      have hcap := c.harena; unfold dimacsBound at hcap
      have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le
      have h2_eq' : (sd.scratch.ant_sz + 2).toNat = sd.scratch.ant_sz.toNat + 2 := by bv_omega
      omega)).toNat = fullArenaClauseSize sp sd.scratch.ant_sz.toNat := by
  intro shdr' sp
  have hcap := c.harena; unfold dimacsBound at hcap
  have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le
  obtain ⟨hsp_p, hrefs_p, hpres_p⟩ :=
    fullSparseInvW_set_hdr_non_gs hspd hsub_ref shdr'
      (sd.core.num_irred + 1#64) nr'
      (by rw [hshdr_eq]; exact bv32_and_not_red_garb shdr)
      (by rw [hshdr_eq]; exact bv32_and_not_red_shrk shdr)
  refine ⟨hsp_p, hrefs_p, (hpres_p _ hsub_ref).1.trans hsub_ng, ?_⟩
  rw [(hpres_p _ hsub_ref).2.1]
  unfold fullArenaClauseSize fullArenaClauseSizeCore
  rw [List.getElem?_eq_getElem h2_lt_s, Option.getD_some]
  have h2_eq' : (sd.scratch.ant_sz + 2).toNat = sd.scratch.ant_sz.toNat + 2 := by bv_omega
  exact congrArg BitVec.toNat (Option.some.inj (by
    rw [← List.getElem?_eq_getElem (by omega : (sd.scratch.ant_sz + 2).toNat <
      sd.core.arena.length), ← List.getElem?_eq_getElem h2_lt_s, h2_eq']))

private theorem s13_finish_deduce_confl {F_cur : List (List Nat)} {s sb1 : FullState}
    {cref : BitVec 32} {confl all_done : Bool} {implied impl_a : BitVec 32}
    (hsb1_core : sb1.core = s.core)
    (hcok0 : confl = true → FullConflictOkW F_cur s)
    (hfal0 : confl = false → implied = 0xFFFFFFFF#32 → all_done = true →
      s.core.confl_type = 0#64 ∧
      ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hdisj : confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ all_done = true)
    (himpla : (confl = true ∧ impl_a = 0xFFFFFFFF#32) ∨ (confl = false ∧ impl_a = implied))
    (heq_ff : impl_a = 0xFFFFFFFF#32) :
    FullVivifySpecs.FullVivConflictOk F_cur sb1 ∨
    sb1.core.confl_type = 0#64 ∧
      ∀ l ∈ fullArenaClauseLits sb1 cref.toNat, sb1.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  rcases himpla with ⟨hc_t, _⟩ | ⟨hc_f, hi_eq⟩
  · left; have hvc := s13_conflictOkW_to_viv (hcok0 hc_t)
    unfold FullVivifySpecs.FullVivConflictOk at hvc ⊢
    unfold fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at hvc ⊢
    rwa [hsb1_core]
  · have him_ff : implied = 0xFFFFFFFF#32 := hi_eq.symm.trans heq_ff
    have hall_t : all_done = true := by
      rcases hdisj with ht | hne | ha
      · rw [hc_f] at ht; cases ht
      · exact absurd him_ff hne
      · exact ha
    obtain ⟨hct0, hfal⟩ := hfal0 hc_f him_ff hall_t
    exact Or.inr ⟨by rw [hsb1_core]; exact hct0, fun l hl => by
      unfold fullArenaClauseLits at hl; rw [hsb1_core] at hl ⊢; exact hfal l hl⟩

private theorem s13_finish_bt_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sm : FullState} (hspm : FullSparseInvW c F0 F_cur sm)
    (hc0 : 0 < (BitVec.ofNat 64 sm.core.cur_level).toNat) :
    sm.core.cur_level ≤ c.max_vars ∧ sm.core.cur_level < 2 ^ 64 ∧ 0 < sm.core.cur_level ∧
      (BitVec.ofNat 64 sm.core.cur_level - 1).toNat = sm.core.cur_level - 1 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have := hspm.2.1.cur_level_le; have := hspm.1.core_ok.trail_end_le
  have := hspm.1.core_ok.cur_vars_le
  have hcv : (BitVec.ofNat 64 sm.core.cur_level).toNat = sm.core.cur_level := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨by omega, by omega, hcv ▸ hc0, ?_⟩
  rw [BitVec.toNat_sub, hcv, h1]; omega

/-- Step-13 `full_viv_finish_m6` satisfies exact canonical
**`FullM6VivBackbone.fullVivFinishM6Spec`**. -/
theorem full_viv_finish_m6_s5_wp (Γ : Env)
    (hDeduce : ∀ a m Q X, step13VivDeduceM6Spec a m Q X →
      Γ "full_viv_deduce_m6" [i64, i32, i32, i32] [i32] a m Q X)
    (hMarkGarb : ∀ a m Q X, fullVivMarkGarbM6Spec a m Q X →
      Γ "full_viv_mark_garb_m6" [i64, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X)
    (hReest : ∀ a m Q X, fullVivReestablishM6Spec a m Q X →
      Γ "full_viv_reestablish_m6" [i64, i32] [] a m Q X)
    (hInst : ∀ a m Q X, fullVivInstM6Spec a m Q X →
      Γ "full_viv_inst_m6" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_viv_finish_m6_body a m Q X := by
  rintro ⟨h, cref, sz, confl, implied, all_done, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, href0, hng0, hsz0, hperm0,
     hcok0, himpl0, hfal0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have htmp0_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    intro k hk
    have hmem := s13_vivTmp_mem_of_perm (by rw [hsp0.1.core_ok.tmp_len_arr]; omega) hperm0 k hk
    exact hsp0.2.1.arena.lits_lt cref.toNat href0 hng0 _ hmem
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_viv_finish_m6_body
  fvt_to_group
  let sb1 : FullState :=
    { s with scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } }
  have hspb1 : FullSparseInvW c F0 F_cur sb1 :=
    s13_sparseInvW_with_ant_res hsp0 0xFFFFFFFFFFFFFFFF#64 0#64
  have hsb1_core : sb1.core = s.core := rfl
  have hsb1_rr : sb1.scratch.red_refs = s.scratch.red_refs := rfl
  have hsb1_sub : M6SubRefOk sb1 sb1.scratch.ant_sz := Or.inl rfl
  have hsb1_ng : sb1.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 →
      sb1.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFE#64 →
      sb1.scratch.ant_sz.toNat ∈ fullArenaClauseRefs sb1 ∧
      fullArenaClauseGarb sb1 sb1.scratch.ant_sz.toNat = false := fun h => absurd rfl h
  have hmb1 : (FullMem c sb1 ⋆ R) m := hm
  clear_value sb1; clear hm
  refine wp_join_group (ts := [i32, .bool])
    (fun (olen, has_ded, ()) md => ∃ sd : FullState,
      FullSparseInvW c F0 F_cur sd ∧
      sd.core.cur_vars = s.core.cur_vars ∧
      fullArenaClauseRefs sd = fullArenaClauseRefs s ∧
      fullArenaClauseGarb sd cref.toNat = false ∧
      fullArenaClauseSize sd cref.toNat = sz.toNat ∧
      fullArenaClauseLits sd cref.toNat = fullArenaClauseLits s cref.toNat ∧
      sd.core.arena_len = s.core.arena_len ∧ sd.core.fuel = s.core.fuel ∧
      sd.core.tmp = s.core.tmp ∧ sd.scratch.red_refs = s.scratch.red_refs ∧
      M6SubRefOk sd sd.scratch.ant_sz ∧
      (sd.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 →
        sd.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFE#64 →
        sd.scratch.ant_sz.toNat ∈ fullArenaClauseRefs sd ∧
        fullArenaClauseGarb sd sd.scratch.ant_sz.toNat = false) ∧
      (sd.scratch.ant_sz = 0xFFFFFFFFFFFFFFFF#64 → has_ded = true →
        olen.toNat ≤ sd.core.cur_vars ∧
        (∀ k < olen.toNat,
          (sd.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * sd.core.cur_vars) ∧
        ((sd.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((sd.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c sd ⋆ R) md) ?_ ?_
  · rintro _ ⟨olen, has_ded, ⟨⟩⟩ md
      ⟨sd, hspd, hcvd, hrefs_d, hng_d, hsz_d, hlits_d, hald, hfld, htmpd, hrrd, hsubd,
       hsubd_ng, hded_ok, hmd⟩
    clear hspb1 hsb1_core hsb1_rr hsb1_sub hsb1_ng hmb1 sb1 hDeduce
    have href_d : cref.toNat ∈ fullArenaClauseRefs sd := hrefs_d ▸ href0
    have hperm_d : ((sd.core.tmp.take sz.toNat).map BitVec.toNat).Perm
        (fullArenaClauseLits sd cref.toNat) := by
      rw [htmpd, hlits_d]; exact hperm0
    have hcr_d_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
    have hcr_d_lt : cref.toNat < sd.core.arena.length := by
      have := (hspd.2.1.arena.refs_wf cref.toNat href_d).1
      have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le; omega
    have hcr_d_bv : (cref.setWidth 64).toNat < sd.core.arena.length := by omega
    have hfl_d_le : sd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfld]; exact Nat.le_refl _
    fvt_to_group
    · have hsub_ne : sd.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
      refine wp_join_group (ts := [])
        (fun () ms => ∃ ss : FullState,
          FullSparseInvW c F0 F_cur ss ∧ ss.core.fuel = sd.core.fuel ∧
          ss.core.arena_len = sd.core.arena_len ∧
          fullArenaClauseRefs ss = fullArenaClauseRefs sd ∧
          ss.scratch.red_refs = sd.scratch.red_refs ∧ (FullMem c ss ⋆ R) ms) ?_ ?_
      · rintro _ ⟨⟩ ms ⟨ss, hsps, hfls, hals, hrefss, hrrs, hms⟩
        fvt_steps
        c0_call hMarkGarb
        refine ⟨c, F0, F_cur, ss, R, rfl, hsps, hrefss ▸ href_d, hms,
          fun sm mm hspm _ halm _ hflm hrefsm hrrm _ hmm => ?_⟩
        have hfl_m_le : sm.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hflm, hfls]; exact hfl_d_le
        refine wp_join_group (ts := [])
          (fun () mf => ∃ sf : FullState,
            FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            sf.core.arena_len = s.core.arena_len ∧ fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
            sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
          (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
            fvt_steps
            exact hQ 1#64 sf mf hspf hflf half hrefsf hrrf (Or.inl rfl) (fun h => by cases h) hmf)
          fun Jb hJb => ?_
        fvt_steps
        · have ⟨hcl_m_le, hcl_m_lt, hpos, htgt⟩ := s13_finish_bt_bounds hspm (by c0_bound)
          c0_call hBacktrack
          refine ⟨c, sm, R, rfl, hspm.1, hcl_m_lt, fun _ => by rw [htgt]; omega,
            hspm.2.1.trail_lits_lt, hmm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hle_bt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat ≤ sm.core.cur_level := by
            rw [htgt]; omega
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hspm hle_bt hlen_bt hpres_bt
              (hw_bt F0 F_cur hspm.2.1 hle_bt)
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          exact hJb () m_bt ⟨_, hsp_bt, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hm_bt⟩
        · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hmm⟩
        · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hmm⟩
      · intro Js hJs
        fvt_steps
        · have hsub_lt_al : sd.scratch.ant_sz.toNat < sd.core.arena_len := by
            have hle := hspd.1.core_ok.arena_len_le
            have hc0 : sd.scratch.ant_sz.toNat <
                (BitVec.ofNat 64 sd.core.arena_len).toNat := by c0_bound
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc0
          have hsub_ne2 : sd.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFE#64 := fun he => by
            have hle := hspd.1.core_ok.arena_len_le
            rw [he] at hsub_lt_al; simp at hsub_lt_al; omega
          obtain ⟨hsub_ref_in, hsub_ng⟩ := hsubd_ng hsub_ne hsub_ne2
          have hsub_lt_ar : sd.scratch.ant_sz.toNat < sd.core.arena.length := by
            have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le; omega
          have h2_eq : (sd.scratch.ant_sz + 2#64).toNat = sd.scratch.ant_sz.toNat + 2 := by
            bv_omega
          have h2_lt : (sd.scratch.ant_sz + 2#64).toNat < sd.core.arena.length := by
            have hwf_a := (hspd.2.1.arena.refs_wf _ hsub_ref_in).2
            have hbd_a := hwf_a.1; have hnx_a := hwf_a.2.1
            have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le
            rw [h2_eq]; omega
          let shdr := sd.core.arena[sd.scratch.ant_sz.toNat]'hsub_lt_ar
          have hshdr_eq : fullArenaHdr sd sd.scratch.ant_sz.toNat = shdr := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem hsub_lt_ar, Option.getD_some]
          fvt_steps
          all_goals try exact hJs () md ⟨sd, hspd, rfl, rfl, rfl, rfl, hmd⟩
          · let hdr_c := sd.core.arena[(cref.setWidth 64).toNat]'hcr_d_bv
            let cgl := hdr_c &&& 0x7FFFF#32
            let shdr' := (shdr &&& ~~~0x7FFFF#32) ||| cgl
            obtain ⟨hsp_g, hrefs_g, _⟩ :=
              fullSparseInvW_set_hdr_non_gs hspd hsub_ref_in shdr'
                sd.core.num_irred sd.core.num_redundant
                (by rw [hshdr_eq]
                    exact bv32_set_glue_garb shdr cgl (bv32_glue_mask_garb hdr_c))
                (by rw [hshdr_eq]
                    exact bv32_set_glue_shrk shdr cgl (bv32_glue_mask_shrk hdr_c))
            exact hJs () _ ⟨_, hsp_g, rfl, rfl, hrefs_g, rfl,
              by refine s13_fullMem_eq ?_ (by assumption); rfl⟩
          · have h2_lt_s : sd.scratch.ant_sz.toNat + 2 < sd.core.arena.length := by
              have := (hspd.2.1.arena.refs_wf _ hsub_ref_in).2.1; omega
            obtain ⟨hsp_p, hrefs_p, hng_p, hsz_p⟩ := s13_finish_promote_irred_inv hspd hsub_ref_in
              hsub_ng hshdr_eq h2_lt_s (sd.core.num_redundant - 1#64)
            refine s13_finish_flag_loop_wp Γ hsp_p (hrefs_p ▸ hsub_ref_in) hng_p ?_ ?_
              fun fl' mf hfl' hmf => by
                fvt_steps
                exact hJs () mf ⟨_, fullSparseInvW_with_flags hsp_p hfl', rfl, rfl, hrefs_p,
                  rfl, hmf⟩
            · have hne_s : sd.scratch.ant_sz.toNat ≠ sd.scratch.ant_sz.toNat + 2 := by omega
              simp only [show (2 : BitVec 64) = 2#64 from rfl, h2_eq, List.getElem_set_ne hne_s]
              simpa only [show (2 : BitVec 64) = 2#64 from rfl, h2_eq] using hsz_p
            · refine s13_fullMem_eq ?_ (by assumption); rfl
          · have h2_lt_s : sd.scratch.ant_sz.toNat + 2 < sd.core.arena.length := by
              have := (hspd.2.1.arena.refs_wf _ hsub_ref_in).2.1; omega
            obtain ⟨hsp_p, hrefs_p, hng_p, hsz_p⟩ := s13_finish_promote_irred_inv hspd hsub_ref_in
              hsub_ng hshdr_eq h2_lt_s sd.core.num_redundant
            refine s13_finish_flag_loop_wp Γ hsp_p (hrefs_p ▸ hsub_ref_in) hng_p ?_ ?_
              fun fl' mf hfl' hmf => by
                fvt_steps
                exact hJs () mf ⟨_, fullSparseInvW_with_flags hsp_p hfl', rfl, rfl, hrefs_p,
                  rfl, hmf⟩
            · have hne_s : sd.scratch.ant_sz.toNat ≠ sd.scratch.ant_sz.toNat + 2 := by omega
              simp only [show (2 : BitVec 64) = 2#64 from rfl, h2_eq, List.getElem_set_ne hne_s]
              simpa only [show (2 : BitVec 64) = 2#64 from rfl, h2_eq] using hsz_p
            · refine s13_fullMem_eq ?_ (by assumption); rfl
        · exact hJs () md ⟨sd, hspd, rfl, rfl, rfl, rfl, hmd⟩
    · refine wp_join_group (ts := []) (fun () mf => mf = md) ?_ ?_
      · rintro _ ⟨⟩ mf hmf; rw [hmf]
        refine wp_join_group (ts := []) (fun () mg => mg = md) ?_ ?_
        · rintro _ ⟨⟩ mg hmg; rw [hmg]
          refine wp_join_group (ts := [])
            (fun () mf => ∃ sf : FullState,
              FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              sf.core.arena_len = s.core.arena_len ∧
              fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
              sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
          · rintro _ ⟨⟩ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
            refine wp_join_group (ts := [])
              (fun () mb => ∃ sb : FullState,
                FullSparseInvW c F0 F_cur sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                sb.core.arena_len = s.core.arena_len ∧
                fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
                sb.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sb ⋆ R) mb) ?_ ?_
            · rintro _ ⟨⟩ mb ⟨sb, hspb, hflb, halb, hrefsb, hrrb, hmb⟩
              c0_call hReest
              refine ⟨c, F0, F_cur, sb, R, rfl, hspb, hrefsb ▸ href0, hmb,
                fun sr mr hspr _ harr halr _ hflr hrrr _ hmr => ?_⟩
              have hrefsr : fullArenaClauseRefs sr = fullArenaClauseRefs sb := by
                unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harr, halr]
              fvt_steps
              exact hQ 1#64 sr mr hspr (by rw [hflr]; exact hflb) (halr.trans halb)
                (hrefsr.trans hrefsb) (hrrr.trans hrrb) (Or.inl rfl) (fun h => by cases h) hmr
            · intro Jb hJb; fvt_steps
              · have ⟨hcl_f_le, hcl_f_lt, hpos, htgt⟩ := s13_finish_bt_bounds hspf (by c0_bound)
                c0_call hBacktrack
                refine ⟨c, sf, R, rfl, hspf.1, hcl_f_lt, fun _ => by rw [htgt]; omega,
                  hspf.2.1.trail_lits_lt, hmf,
                  fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                    hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                have hle_bt : (BitVec.ofNat 64 sf.core.cur_level - 1).toNat ≤
                    sf.core.cur_level := by rw [htgt]; omega
                have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                  FullVivTop.FullSparseInvW.of_backtrack hspf hle_bt hlen_bt hpres_bt
                    (hw_bt F0 F_cur hspf.2.1 hle_bt)
                rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                exact hJb () m_bt ⟨_, hsp_bt, hflf, half, hrefsf, hrrf, hm_bt⟩
              · exact hJb () mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
              · exact hJb () mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
          · intro Ji hJi
            clear hMarkGarb hBacktrack hCommit hded_ok hsubd hsubd_ng hcok0 himpl0 hfal0
            fvt_steps
            all_goals try exact hJi () md ⟨sd, hspd, hfl_d_le, hald, hrefs_d, hrrd, hmd⟩
            c0_call hInst
            refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hng_d, hsz_d, hsz_le, hperm_d, hmd,
              fun ir s_i m_i hspi hfli hali hrefsi hrri hir h20i hm_i => ?_⟩
            have hfli' : s_i.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfli hfl_d_le
            fvt_steps
            · have hir_ne0 : ir ≠ 0#64 := by c0_bound
              have hir_12 : ir = 1#64 ∨ ir = 2#64 ∨ ir = 20#64 := hir.resolve_left hir_ne0
              c0_call hReest
              refine ⟨c, F0, F_cur, s_i, R, rfl, hspi, hrefsi ▸ href_d, hm_i,
                fun sr mr hspr _ harr halr _ hflr hrrr _ hmr => ?_⟩
              have hrefsr : fullArenaClauseRefs sr = fullArenaClauseRefs s_i := by
                unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harr, halr]
              fvt_steps; apply hJ; fvt_steps
              exact hQ ir sr mr hspr (by rw [hflr]; exact hfli')
                (halr.trans (hali.trans hald)) (hrefsr.trans (hrefsi.trans hrefs_d))
                (hrrr.trans (hrri.trans hrrd)) hir_12 h20i hmr
            · have hir_ne0 : ir ≠ 0#64 := by c0_bound
              have hir_12 : ir = 1#64 ∨ ir = 2#64 ∨ ir = 20#64 := hir.resolve_left hir_ne0
              exact hQ ir s_i m_i hspi hfli' (hali.trans hald) (hrefsi.trans hrefs_d)
                (hrri.trans hrrd) hir_12 h20i hm_i
            · exact hJi () m_i ⟨s_i, hspi, hfli', hali.trans hald, hrefsi.trans hrefs_d,
                hrri.trans hrrd, hm_i⟩
        · intro Jg hJg
          clear hCommit hReest hInst hperm0 hperm_d htmp0_lt hcok0 himpl0 hfal0
            hsz_le hded_ok hsubd hsubd_ng
          fvt_to_group
          · refine wp_join_group (ts := []) (fun () m1 => m1 = md)
              (fun _ _ m1 hm1 => by
                rw [hm1]
                refine wp_join_group (ts := []) (fun () m2 => m2 = md)
                  (fun _ _ m2 hm2 => by
                    rw [hm2]
                    c0_call hMarkGarb
                    refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hmd,
                      fun sm mm hspm _ halm _ hflm hrefsm hrrm _ hmm => ?_⟩
                    have hcl_m_le : sm.core.cur_level ≤ c.max_vars := by
                      have := hspm.2.1.cur_level_le; have := hspm.1.core_ok.trail_end_le
                      have := hspm.1.core_ok.cur_vars_le; omega
                    have hcl_m_lt : sm.core.cur_level < 2 ^ 64 := by omega
                    have hfl_m_le : sm.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [hflm]; exact hfl_d_le
                    refine wp_join_group (ts := [])
                      (fun () mf => ∃ sf : FullState,
                        FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        sf.core.arena_len = s.core.arena_len ∧
                        fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
                        sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
                      (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
                        fvt_steps
                        exact hQ 1#64 sf mf hspf hflf half hrefsf hrrf (Or.inl rfl)
                          (fun h => by cases h) hmf)
                      fun Jb hJb => ?_
                    fvt_steps
                    · have ⟨hcl_m_le, hcl_m_lt, hpos, htgt⟩ :=
                        s13_finish_bt_bounds hspm (by c0_bound)
                      have hle_bt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat ≤
                          sm.core.cur_level := by rw [htgt]; omega
                      c0_call hBacktrack
                      refine ⟨c, sm, R, rfl, hspm.1, hcl_m_lt, fun _ => by rw [htgt]; omega,
                        hspm.2.1.trail_lits_lt, hmm,
                        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                          hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                      have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                        FullVivTop.FullSparseInvW.of_backtrack hspm hle_bt hlen_bt hpres_bt
                          (hw_bt F0 F_cur hspm.2.1 hle_bt)
                      rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                      exact hJb () m_bt ⟨_, hsp_bt, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hm_bt⟩
                    · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hmm⟩
                    · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hmm⟩)
                  fun Jm2 hJm2 => by
                    fvt_steps
                    all_goals first | exact hJm2 () md rfl | exact hJg () md rfl)
              fun Jm hJm => by
                fvt_steps
                all_goals first | exact hJm () md rfl | exact hJg () md rfl
          · exact hJg () md rfl
      · intro Jc hJc
        fvt_to_group
        · have hhd_t : has_ded = true := by assumption
          have hsub_ff : sd.scratch.ant_sz = 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
          obtain ⟨hol_cv, hws_lt, hws_nd, hws_ent⟩ := hded_ok hsub_ff hhd_t
          have hol_mv : olen.toNat ≤ c.max_vars := by
            have := hspd.1.core_ok.cur_vars_le; omega
          refine wp_join_group (ts := [i32]) (fun _ m2 => m2 = md)
            (fun _ ⟨_impl_arg, ⟨⟩⟩ m2 hm2 => by
              rw [hm2]
              c0_call hCommit
              refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hng_d, hol_mv,
                fun _ => ⟨hws_lt, hws_nd, hws_ent⟩, hmd,
                fun cr s_c m_c hspc _ halc _ hflc hrefsc hrrc _ hcr h20c hm_c => ?_⟩
              refine wp_join_group (ts := [])
                (fun () mf => ∃ sf : FullState,
                  FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  sf.core.arena_len = s.core.arena_len ∧
                  fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
                  sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
                (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
                  fvt_steps; exact hQ cr sf mf hspf hflf half hrefsf hrrf hcr h20c hmf)
                fun Jr hJr => ?_
              fvt_steps
              · c0_call hReest
                refine ⟨c, F0, F_cur, s_c, R, rfl, hspc, hrefsc ▸ href_d, hm_c,
                  fun s_r m_r hspr _ har_r hal_r _ hfl_r hrr_r _ hm_r => ?_⟩
                have hrefs_r : fullArenaClauseRefs s_r = fullArenaClauseRefs s_c := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har_r, hal_r]
                exact hJr () m_r ⟨s_r, hspr, by rw [hfl_r, hflc]; exact hfl_d_le,
                  hal_r.trans (halc.trans hald), hrefs_r.trans (hrefsc.trans hrefs_d),
                  hrr_r.trans (hrrc.trans hrrd), hm_r⟩
              · exact hJr () m_c ⟨s_c, hspc, by rw [hflc]; exact hfl_d_le, halc.trans hald,
                  hrefsc.trans hrefs_d, hrrc.trans hrrd, hm_c⟩)
            fun Jt hJt => by fvt_steps <;> exact hJt _ md rfl
        · exact hJc () md rfl
        · exact hJc () md rfl
  · intro Jif hJif
    clear hMarkGarb hBacktrack hCommit hReest hInst hperm0
    have href_b1 : cref.toNat ∈ fullArenaClauseRefs sb1 := by
      unfold fullArenaClauseRefs; rw [hsb1_core]; exact href0
    have hng_b1 : fullArenaClauseGarb sb1 cref.toNat = false := by
      unfold fullArenaClauseGarb; rw [hsb1_core]; exact hng0
    have hsz_b1 : fullArenaClauseSize sb1 cref.toNat = sz.toNat := by
      unfold fullArenaClauseSize; rw [hsb1_core]; exact hsz0
    have hlits_b1 : fullArenaClauseLits sb1 cref.toNat = fullArenaClauseLits s cref.toNat := by
      unfold fullArenaClauseLits; rw [hsb1_core]
    have htmp_b1 : ∀ k < sz.toNat, (sb1.core.tmp[k]?.getD 0#32).toNat < 2 * sb1.core.cur_vars := by
      rw [hsb1_core]; exact htmp0_lt
    have hcv_b1 : sb1.core.cur_vars = s.core.cur_vars := congrArg FullCoreState.cur_vars hsb1_core
    have hal_b1 : sb1.core.arena_len = s.core.arena_len :=
      congrArg FullCoreState.arena_len hsb1_core
    have hfl_b1 : sb1.core.fuel = s.core.fuel := congrArg FullCoreState.fuel hsb1_core
    have htm_b1 : sb1.core.tmp = s.core.tmp := congrArg FullCoreState.tmp hsb1_core
    fvt_to_group
    refine wp_join_group (ts := [])
      (fun () m1 => m1 = m ∧ (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ all_done = true))
      (fun _ _ m1 ⟨hm1, hdisj⟩ => by
        rw [hm1]
        refine wp_join_group (ts := [i32])
          (fun (impl_a, ()) m2 => m2 = m ∧
            ((confl = true ∧ impl_a = 0xFFFFFFFF#32) ∨ (confl = false ∧ impl_a = implied)))
          (fun _ ⟨impl_a, ⟨⟩⟩ m2 ⟨hm2, himpla⟩ => by
            rw [hm2]
            c0_call hDeduce
            refine ⟨c, F0, F_cur, sb1, R, rfl, hspb1, href_b1, hng_b1,
              hsz_le, htmp_b1, fun heq_ff => ?_, fun hne_ff => ?_, hmb1,
              fun olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' md hspd hsubd hsubd_ng
                hrefsd hpresd hol_ok hmd => ?_⟩
            · exact s13_finish_deduce_confl hsb1_core hcok0 hfal0 hdisj himpla heq_ff
            · rcases himpla with ⟨_, hi_ff⟩ | ⟨hc_f, hi_eq⟩
              · exact absurd hi_ff hne_ff
              · subst hi_eq
                obtain ⟨him_lt, him_val⟩ := himpl0 hc_f hne_ff
                exact ⟨by rw [hcv_b1]; exact him_lt, by rw [hsb1_core]; exact him_val⟩
            · fvt_steps
              have hpres_c := hpresd cref.toNat href_b1
              have hrefs_s : fullArenaClauseRefs sb1 = fullArenaClauseRefs s := by
                unfold fullArenaClauseRefs; rw [hsb1_core]
              exact hJif (olen, olen != 0xFFFFFFFF#32, ()) md
                ⟨_, hspd, hcv_b1, hrefsd.trans hrefs_s, hpres_c.1.trans hng_b1,
                 hpres_c.2.1.trans hsz_b1, hpres_c.2.2.trans hlits_b1, hal_b1, hfl_b1, htm_b1,
                 hsb1_rr, hsubd, hsubd_ng,
                 fun ha hd => hol_ok ha (by
                   revert hd; cases Decidable.em (olen = 0xFFFFFFFF#32) <;> simp [*]), hmd⟩)
          fun Jt hJt => by
            fvt_steps
            · exact hJt _ m ⟨rfl, Or.inl ⟨by assumption, rfl⟩⟩
            · exact hJt _ m ⟨rfl, Or.inr ⟨by assumption, rfl⟩⟩)
      fun Jthen hJthen => by
        fvt_steps
        · exact hJthen () m ⟨rfl, Or.inl (by assumption)⟩
        · exact hJthen () m ⟨rfl, Or.inr (Or.inl (by c0_bound))⟩
        · exact hJthen () m ⟨rfl, Or.inr (Or.inr (by assumption))⟩
        · exact hJif (sz, false, ()) m
            ⟨sb1, hspb1, hcv_b1, by unfold fullArenaClauseRefs; rw [hsb1_core], hng_b1,
             hsz_b1, hlits_b1, hal_b1, hfl_b1, htm_b1, hsb1_rr,
             hsb1_sub, hsb1_ng, (fun _ hd => by cases hd), hmb1⟩

end FinishProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
