module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof1
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb


/-!
# Kissat Wave-2 PR-W2C (`RC-20`) — Vivification Deduce & Subsumption (`Proof2b`)

Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for
`full_viv_deduce_m6` (`fullVivDeduceM6Spec`, `M6SubRefOk` in `h->ant_sz`, backward
BFS entailment, and `mrk`/`lit_mark` restoration).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Cross-File Specifications (`Simplify`, `Commit`, `Deduce`) -/

section Specs

/-- Valid subsumption-clause witness stored in `h->ant_sz` by `full_viv_deduce_m6`:
none (`0xFFFFFFFFFFFFFFFF#64`), binary (`0xFFFFFFFFFFFFFFFE#64`), or a valid arena clause ref. -/
@[expose] def M6SubRefOk (s : FullState) (sub_ref : BitVec 64) : Prop :=
  sub_ref = 0xFFFFFFFFFFFFFFFF#64 ∨ sub_ref = 0xFFFFFFFFFFFFFFFE#64 ∨
  sub_ref.toNat ∈ fullArenaClauseRefs s

/-- Specification for `full_viv_deduce_m6(h, cref, sz, implied)`: backward unit/reason analysis
with binary/large subsumption tracking (`M6SubRefOk` in `ant_sz`), restoring `mrk` and `lit_mark`
and certifying `F_cur ⊨ work_stk2[0 ..< olen)` whenever `olen ≠ 0xFFFFFFFF#32`. -/
@[expose] def fullVivDeduceM6Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, cref, sz, implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (implied = 0xFFFFFFFF#32 →
        FullVivifySpecs.FullVivConflictOk F_cur s ∨
        (s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen mrk' lm' ws1' ws2' asz' rsz' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', lit_mark := lm' }
            scratch := { s.scratch with
              work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
        FullSparseInvW c F0 F_cur s' → M6SubRefOk s asz' →
        (olen ≠ 0xFFFFFFFF#32 →
          olen.toNat ≤ s.core.cur_vars ∧
          (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

end Specs


private theorem c0_store_ws1_z_m6b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_store_ws1_b_m6b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_store_ws2_z_m6b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

private theorem c0_store_ws2_b_m6b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

attribute [local c0_store] c0_store_ws1_z_m6b c0_store_ws1_b_m6b
  c0_store_ws2_z_m6b c0_store_ws2_b_m6b

/-! ## 5. `full_viv_deduce_m6_wp` -/

section DeduceProof

open FullVivifyHelpers

private theorem m6_vivClosed_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qi qlen olen olen' : Nat} {taut : Bool}
    (hcb : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen olen' true := by
  intro k hk idx hidx ht
  rcases (by omega : k < qi ∨ k = qi) with hk' | rfl
  · have h := hcb k hk' idx hidx ht
    by_cases hr : s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · simp only [hr, ↓reduceIte]; intro h1; cases h1
    · simp only [hr, ↓reduceIte] at h ⊢; exact h
  · simp only [hrsn, ↓reduceIte]; intro h1; cases h1

private theorem m6_vivSeed_mono_ws2 {s : FullState} {cref implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qlen olen olen' : Nat}
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen false)
    (hle : olen ≤ olen') (hlen : olen ≤ ws2.length) (hlen' : olen' ≤ ws2'.length)
    (hpre : ∀ j < olen, ws2'[j]? = ws2[j]?) :
    VivSeedOk s cref implied ws1 ws2' qlen olen' false := by
  intro _
  have h := hsd rfl
  by_cases hi : implied = 0xFFFFFFFF#32
  · simp only [hi, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢; exact h
  · simp only [hi, ne_eq, not_false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨j, hj, hjeq⟩ := (mem_map_take_iff hlen).mp h
    exact (mem_map_take_iff hlen').mpr ⟨j, by omega, by rw [hpre j hj, hjeq]⟩

private theorem m6_fullMem_mrk_ws1_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {mrk1 mrk2 lm : List (BitVec 8)} {ws1_1 ws1_2 : List (BitVec 32)}
    {asz rsz : BitVec 64} (hmrk : mrk1 = mrk2) (hws1 : ws1_1 = ws1_2)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk1, lit_mark := lm }
      scratch := { s.scratch with work_stk1 := ws1_1, ant_sz := asz, res_sz := rsz } } ⋆ R) m) :
    (FullMem c { s with
      core := { s.core with mrk := mrk2, lit_mark := lm }
      scratch := { s.scratch with work_stk1 := ws1_2, ant_sz := asz, res_sz := rsz } } ⋆ R) m := by
  subst hmrk; subst hws1; exact hm

private theorem m6_subRef_set_ref {s : FullState} {r : BitVec 32}
    (hr : r.toNat ∈ fullArenaClauseRefs s) : M6SubRefOk s (r.setWidth 64) :=
  Or.inr (Or.inr (by
    simpa [BitVec.toNat_setWidth,
      (Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide : 2 ^ 32 < 2 ^ 64)))] using hr))

private theorem m6_deduce_finish_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars)
    (hmrk_clr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :=
  ⟨⟨{ hsp.1.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
    { hsp.1.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hmrk_clr, hlm_clr⟩, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_deduce_state_len {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with
      core := { s.core with mrk := mrk', lit_mark := lm' }
      scratch := { s.scratch with
        work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :
      FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
   { hlen.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩

private theorem m6_deduce_state_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    {mrk' lm' : List (BitVec 8)} :
    FullWitnessInv c F0 F_cur { s.core with mrk := mrk', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem m6_push_branch_step {c : FullCfg}
    {s : FullState} {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)}
    {asz_c rsz_c : BitVec 64} {qlen : Val i64} {ov : Val i32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost} {J : Cont [i64]} {Γ : Env}
    (hlen : s.LengthsOk c) (hq : VivQueueOk c s mrk_c ws1_c qlen.toNat)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hov_trl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = ov.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_c, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) mn,
      qlen.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen.toNat, ws1_n[j]? = ws1_c[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      ((s.core.lvl[ov.toNat]?.getD 0#32).toNat = 0 ∨
        ov.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mn →
      J (qlen', ()) mn) :
    wp Γ Q X (deducePushExpr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 ov qlen J) m := by
  have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hov_lvl : ov.toNat < s.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hov_mrk : ov.toNat < mrk_c.length := by rw [hq.1]; omega
  have hql_le := hq.2.2.1; have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
  dsimp only [deducePushExpr, fvOp32]
  fvt_steps
  · have hlvl_pos : 0 < (s.core.lvl[ov.toNat]'hov_lvl).toNat := by c0_bound
    have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hlvl_pos' : 0 < (s.core.lvl[ov.toNat]?.getD 0#32).toNat := by
      rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some]
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hql_ws1 : qlen.toNat < ws1_c.length := by have := hq.2.1; omega
    have hql1 : (qlen + 1#64).toNat = qlen.toNat + 1 := by bv_omega
    obtain ⟨_, hq_next, hpre_next, _⟩ :=
      push_queue_step hq hcv_le hov_lt hlvl_pos' hm0' hov_trl
    fvt_steps
    have hov_mod : ov.toNat % 2 ^ 64 = ov.toNat := Nat.mod_eq_of_lt (by omega)
    refine hJ (qlen + 1#64) _ _ _ (by omega) (by omega) hpre_next ?_ (Or.inr ?_) hm
    · simpa [hql1, hov_mod] using hq_next
    · rw [hql1]
      exact (mem_map_take_iff (by simp [hq.2.1]; omega)).mpr
        ⟨qlen.toNat, by omega, by rw [List.getElem?_set_self hql_ws1]; rfl⟩
  · have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hcv_le_q : s.core.cur_vars % 2 ^ 64 ≤ qlen.toNat := by c0_bound
    rw [Nat.mod_eq_of_lt hcv_64] at hcv_le_q; omega
  · have hm_ne0 : mrk_c[ov.toNat]'hov_mrk ≠ 0#8 := fun h => by
      have hne32 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 ≠ 0#32 := by assumption
      exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
    have hm1 : mrk_c[ov.toNat]?.getD 0#8 = 1#8 := by
      rcases hq.2.2.2.2.2.2.2.1 ov.toNat hov_lt with h0 | h1
      · rw [List.getElem?_eq_getElem hov_mrk, Option.getD_some] at h0; exact absurd h0 hm_ne0
      · exact h1
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inr ((hq.2.2.2.2.2.2.1 ov.toNat hov_lt).mp hm1)) hm
  · have hlvl0 : (s.core.lvl[ov.toNat]'hov_lvl).toNat = 0 := by c0_bound
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inl (by rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some])) hm


private abbrev m6DeduceClearExpr (h pMark pLitMark pTmp pWs1 : Val i64)
    (sz : Val i32) (qlen : Val i64) (olen : Val i32) (taut : Val .bool) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p19 =>
    fvOp32 (OpCode.cmp .ult i64 .bool (by decide)) (Arg.var p19.fst, Arg.var qlen, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.mul i64) (Arg.var p19.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld =>
       fvOp32 (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
       fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
       Expr.store (Arg.var p0.fst) (Arg.var p.fst)
         (fvOp32 (OpCode.add i64) (Arg.var p19.fst, Arg.imm 1, ()) fun p =>
          Expr.jump Js.fst (Arg.var p.fst, ())))
      (Expr.group (sig := [[i32]]) (fun Js2 => Blocks.cons (fun p21 =>
        fvOp32 (OpCode.cmp .ult i32 .bool (by decide)) (Arg.var p21.fst, Arg.var sz, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.zext 32 64) (Arg.var p21.fst, ()) fun p =>
           fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var pTmp, Arg.var p.fst, ()) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld =>
           fvOp32 (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var pLitMark, Arg.var p.fst, ()) fun p =>
           fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
           Expr.store (Arg.var p0.fst) (Arg.var p.fst)
             (fvOp32 (OpCode.add i32) (Arg.var p21.fst, Arg.imm 1, ()) fun p =>
              Expr.jump Js2.fst (Arg.var p.fst, ())))
          (Expr.jnz (Arg.var taut)
            (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.store (Arg.imm (t := i64) 18446744073709551615) (Arg.var p.fst)
               (Expr.ret (Arg.imm 4294967295, ())))
            (Expr.ret (Arg.var olen, ())))) Blocks.nil)
        fun Js2 => Expr.jump Js2.fst (Arg.imm 0, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem m6_deduce_clear_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {sz : Val i32} {qlen_c : Val i64} {olen_c : Val i32} {taut_c : Val .bool}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hsub_b : M6SubRefOk s asz_b)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hQ : ∀ (ret : Val i32) mrk' lm' asz' mf,
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz', res_sz := rsz_b } }
      FullSparseInvW c F0 F_cur s' → M6SubRefOk s asz' →
      (taut_c = true → ret = 0xFFFFFFFF#32) → (taut_c = false → ret = olen_c) →
      (FullMem c s' ⋆ R) mf → Q (ret, ()) mf) :
    wp Γ Q X (m6DeduceClearExpr c.hdr c.pMark c.pLitMark c.pTmp c.pWorkStk1
      sz qlen_c olen_c taut_c) m := by
  have hcl := hspW.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  dsimp only [m6DeduceClearExpr, fvOp32]
  refine wp_loop_inv (ts := [i64])
    (fun (qi2, ()) mc => ∃ mrk_c : List (BitVec 8),
      qi2.toNat ≤ qlen_c.toNat ∧ mrk_c.length = c.max_vars ∧
      (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 ∨
        ∃ k, qi2.toNat ≤ k ∧ k < qlen_c.toNat ∧ (ws1_b[k]?.getD 0#32).toNat = v) ∧
      (FullMem c { s with
        core := { s.core with mrk := mrk_c, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mc)
    (fun (qi2, ()) _ => qlen_c.toNat - qi2.toNat) ?_ ?_
  · intro Jc hJc; fvt_steps
    exact hJc (0#64, ()) m ⟨mrk_b, by simp, hqb.1, viv_clear_mrk_init hqb hcv_le, hm⟩
  · rintro Jc ⟨qi2, ⟨⟩⟩ mc ⟨mrk_c, hq2_le, hmrkc_len, hinv_c, hmc⟩ ihc
    fvt_step; fvt_step
    · have hqi2_lt : qi2.toNat < qlen_c.toNat := by c0_bound
      have hqi2_ws1 : qi2.toNat < ws1_b.length := by have := hqb.2.1; have := hqb.2.2.1; omega
      have hqi2_1 : (qi2 + 1#64).toNat = qi2.toNat + 1 := by bv_omega
      obtain ⟨hv_mrk, hinv_next⟩ := viv_clear_mrk_step hmrkc_len hqb.2.2.2.1 hcv_le hqi2_lt hinv_c
      have hidx_mrk : (ws1_b[qi2.toNat]'hqi2_ws1).toNat < mrk_c.length := by
        rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some] at hv_mrk
      have hidx_set64 : ((ws1_b[qi2.toNat]'hqi2_ws1).setWidth 64).toNat =
          (ws1_b[qi2.toNat]'hqi2_ws1).toNat := by bv_omega
      have hidx_mrk64 : ((ws1_b[qi2.toNat]'hqi2_ws1).setWidth 64).toNat < mrk_c.length := by
        rw [hidx_set64]; exact hidx_mrk
      have hidx_mod : (ws1_b[qi2.toNat]'hqi2_ws1).toNat % 2 ^ 64 =
          (ws1_b[qi2.toNat]'hqi2_ws1).toNat :=
        Nat.mod_eq_of_lt (Nat.lt_trans (ws1_b[qi2.toNat]'hqi2_ws1).isLt (by decide))
      fvt_steps; simp only [hidx_mod] at *
      exact ihc (qi2 + 1#64, ()) _ (by dsimp only; omega)
        ⟨mrk_c.set (ws1_b[qi2.toNat]'hqi2_ws1).toNat 0#8, by dsimp only; omega, by simp [hmrkc_len],
         fun u hu => by
           have h := hinv_next u hu
           rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some, ← hqi2_1] at h, by assumption⟩
    · have hqi2_eq : qi2.toNat = qlen_c.toNat := by c0_bound
      have hmrkc_clr : ∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 := fun v hv => by
        rcases hinv_c v hv with h0 | ⟨k, hk1, hk2, _⟩
        · exact h0
        · omega
      clear hc ihc Jc
      refine wp_loop_inv (ts := [i32])
        (fun (mi2, ()) mlm =>
          mi2.toNat ≤ sz.toNat ∧ ∃ lm2 : List (BitVec 8), lm2.length = 2 * c.max_vars ∧
            (∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 ≠ 0#8 →
              ∃ t, mi2.toNat ≤ t ∧ t < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_c, lit_mark := lm2 }
              scratch := { s.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
              ⋆ R) mlm)
        (fun (mi2, _) _ => sz.toNat - mi2.toNat) ?_ ?_
      · intro Jl hJl; fvt_steps
        exact hJl (0#32, ()) mc ⟨Nat.zero_le _, lm1, hlm1_len, fun l hl hnz => by
          obtain ⟨t, ht, hteq⟩ := hlm1_dom l hl hnz
          exact ⟨t, Nat.zero_le _, by omega, hteq⟩, hmc⟩
      · rintro Jl ⟨mi2, ⟨⟩⟩ mlm ⟨hmi2_le, lm2, hlm2_len, hlm2_dom, hmlm⟩ ihl
        fvt_step; fvt_step
        · have hmi2_lt : mi2.toNat < sz.toNat := by c0_bound
          have hmi2_1 : (mi2 + 1#32).toNat = mi2.toNat + 1 := by bv_omega
          have hmi2_tmp : mi2.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
          let lt2 := s.core.tmp[mi2.toNat]'hmi2_tmp
          have hlt2_lm : lt2.toNat < lm2.length := by
            have := htmp_lt mi2.toNat hmi2_lt
            rw [List.getElem?_eq_getElem hmi2_tmp, Option.getD_some] at this
            dsimp only [lt2]; omega
          fvt_steps
          let lm2' := lm2.set lt2.toNat 0#8
          refine ihl (mi2 + 1#32, ()) _ (by dsimp only; omega)
            ⟨by omega, lm2', by simp [lm2', hlm2_len], fun q hq hnz => ?_, by assumption⟩
          by_cases hql : q = lt2.toNat
          · subst hql; dsimp only [lm2'] at hnz
            rw [List.getElem?_set_self hlt2_lm, Option.getD_some] at hnz; exact absurd rfl hnz
          · dsimp only [lm2'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
            obtain ⟨t, ht1, ht2, hteq⟩ := hlm2_dom q hq hnz
            have hne_t : t ≠ mi2.toNat := fun he => by
              subst he; rw [List.getElem?_eq_getElem hmi2_tmp, Option.getD_some] at hteq
              exact hql hteq.symm
            exact ⟨t, by omega, ht2, hteq⟩
        · have hmi2_eq : mi2.toNat = sz.toNat := by c0_bound
          have hlm2_clr : ∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 = 0#8 := fun l hl =>
            Classical.byContradiction fun hnz => by
              obtain ⟨t, ht1, ht2, _⟩ := hlm2_dom l hl hnz; omega
          fvt_steps
          · exact hQ 0xFFFFFFFF#32 mrk_c lm2 0xFFFFFFFFFFFFFFFF#64 _
              (m6_deduce_finish_sparse hspW hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
              (Or.inl rfl) (fun _ => rfl) (fun h => by cases h.symm.trans hc) hm
          · exact hQ olen_c mrk_c lm2 asz_b mlm
              (m6_deduce_finish_sparse hspW hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
              hsub_b (fun h => by cases h.symm.trans hc) (fun _ => rfl) hmlm

private abbrev m6DeduceLargeRsnExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref sz rsn_bv v_bv : Val i32) (qlen : Val i64) (J : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_13 =>
  fvOp32 (OpCode.cmp .ule i64 .bool (by decide)) (Arg.var p3.fst, Arg.var ld_13, ()) fun pb =>
  Expr.jnz (Arg.var pb.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
        fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld_14 =>
        Expr.group (sig := [[i64, i32]]) (fun Js_2 => Blocks.cons (fun p_38 =>
          fvOp32 (OpCode.cmp .ult i32 .bool (by decide))
            (Arg.var p_38.snd.fst, Arg.var ld_14, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
             fvOp32 (OpCode.zext 32 64) (Arg.var ld_14, ()) fun pz =>
             fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
             Expr.load i64 (Arg.var p48.fst) fun ld_15 =>
             fvOp32 (OpCode.cmp .ule i64 .bool (by decide))
               (Arg.var p.fst, Arg.var ld_15, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
                fvOp32 (OpCode.zext 32 64) (Arg.var p_38.snd.fst, ()) fun pz =>
                fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                fvOp32 (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_ov =>
                Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                  fvOp32 (OpCode.add i32) (Arg.var p_38.snd.fst, Arg.imm 1, ()) fun pj =>
                  Expr.jump Js_2.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil) fun Js_n =>
                fvOp32 (OpCode.cmp .ne i32 .bool (by decide))
                  (Arg.var p_ov.fst, Arg.var v_bv, ()) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_38.fst Js_n.fst)
                  (Expr.jump Js_n.fst (Arg.var p_38.fst, ())))
               (Expr.jump J (Arg.var p_38.fst, ())))
            (Expr.jump J (Arg.var p_38.fst, ()))) Blocks.nil)
          fun Js_init => Expr.jump Js_init.fst (Arg.var qlen, Arg.imm 0, ())) Blocks.nil)
        fun Js_as =>
        fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp32 (OpCode.cmp .eq i64 .bool (by decide))
          (Arg.var ld, Arg.imm 18446744073709551615, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var rsn_bv, Arg.var cref, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (Expr.call "full_viv_subsumes_cl_m6" (as := [i64, i32, i32]) (bs := [.bool])
                (Arg.var h, Arg.var rsn_bv, Arg.var sz, ()) fun ok =>
              Expr.jnz (Arg.var ok.fst)
                (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun pr =>
                 fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
                 Expr.store (Arg.var pr.fst) (Arg.var p.fst) (Expr.jump Js_as.fst ()))
                (Expr.jump Js_as.fst ()))
             (Expr.jump Js_as.fst ()))
          (Expr.jump Js_as.fst ())) Blocks.nil)
      fun Js_rs =>
      fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
      fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      fvOp32 (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
      fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
         Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.jump Js_rs.fst ()))
        (Expr.jump Js_rs.fst ()))
    (Expr.jump J (Arg.var qlen, ()))

private theorem m6_deduce_large_rsn_wp (Γ : Env)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {qlen_c : Val i64} {cref sz rsn_bv v_bv : Val i32} {idx0 : Nat} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} {J : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars) (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hsub_b : M6SubRefOk s asz_b)
    (href_r : rsn_bv.toNat ∈ fullArenaClauseRefs s)
    (hng_r : fullArenaClauseGarb s rsn_bv.toNat = false)
    (hidx0 : idx0 < s.core.trail_end) (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hlits_r : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32))
        (asz_n rsz_n : BitVec 64) mlg,
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat → M6SubRefOk s asz_n →
      (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_n, res_sz := rsz_n } } ⋆ R) mlg →
      J (qlen', ()) mlg) :
    wp Γ Q X (m6DeduceLargeRsnExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref sz rsn_bv v_bv qlen_c J) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hwf_r := hw.arena.refs_wf rsn_bv.toNat href_r
  have hbd_r :
      rsn_bv.toNat + 3 + fullArenaClauseSizeCore s.core rsn_bv.toNat ≤ s.core.arena.length := by
    omega
  dsimp only [m6DeduceLargeRsnExpr, fvOp32]
  fvt_to_group
  · have hrsn_ar : rsn_bv.toNat < s.core.arena.length := by omega
    have hrsn_2 : (rsn_bv.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
    have hrsn_2_mod : (rsn_bv.toNat + 2) % 18446744073709551616 = rsn_bv.toNat + 2 :=
      Nat.mod_eq_of_lt (by have := hwf_r.1; omega)
    have hrsn_2_eq : (rsn_bv.setWidth 64 + 2#64).toNat = rsn_bv.toNat + 2 := by bv_omega
    let rsz_bv := s.core.arena[(rsn_bv.setWidth 64 + 2#64).toNat]'hrsn_2
    have hrsz_raw : s.core.arena[rsn_bv.toNat + 2]'(by omega) = rsz_bv := by
      dsimp only [rsz_bv]; simp only [hrsn_2_eq]
    have hrsz_eq : rsz_bv.toNat = fullArenaClauseSizeCore s.core rsn_bv.toNat := by
      unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat hrsz_raw.symm
    refine wp_join_group (ts := [])
      (fun _ m_rs => ∃ rsz_1 : BitVec 64,
        (FullMem c { s with
          core := { s.core with mrk := mrk_b, lit_mark := lm1 }
          scratch := { s.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_1 } } ⋆ R) m_rs)
      (fun _ _ m_rs ⟨rsz_1, hm_rs⟩ => by
        refine wp_join_group (ts := [])
          (fun _ m_as => ∃ asz_1 : BitVec 64, M6SubRefOk s asz_1 ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_b, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_1, res_sz := rsz_1 } }
              ⋆ R) m_as)
          (fun _ _ m_as ⟨asz_1, hsub_1, hm_as⟩ => by
            fvt_to_group
            refine wp_loop_inv (ts := [i64, i32])
              (fun (qlen_j, j_c, ()) mj => ∃ (mrk_j : List (BitVec 8)) (ws1_j : List (BitVec 32)),
                j_c.toNat ≤ rsz_bv.toNat ∧ qlen_c.toNat ≤ qlen_j.toNat ∧
                qlen_j.toNat ≤ s.core.cur_vars ∧ (∀ k < qlen_c.toNat, ws1_j[k]? = ws1_b[k]?) ∧
                VivQueueOk c s mrk_j ws1_j qlen_j.toNat ∧
                (∀ t < j_c.toNat,
                  (s.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ≠ v_bv.toNat →
                  (s.core.lvl[(s.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat = 0 ∨
                  (s.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
                    (ws1_j.take qlen_j.toNat).map BitVec.toNat) ∧
                (FullMem c { s with
                  core := { s.core with mrk := mrk_j, lit_mark := lm1 }
                  scratch := { s.scratch with
                    work_stk1 := ws1_j, work_stk2 := ws2_b,
                    ant_sz := asz_1, res_sz := rsz_1 } } ⋆ R) mj)
              (fun (_, j_c, ()) _ => rsz_bv.toNat - j_c.toNat) ?_ ?_
            · intro Jj hJj; fvt_steps
              exact hJj (qlen_c, 0#32, ()) m_as ⟨mrk_b, ws1_b, by simp, Nat.le_refl _, hqb.2.2.1,
                fun _ _ => rfl, hqb, fun _ h => absurd h (Nat.not_lt_zero _), hm_as⟩
            · rintro Jj ⟨qlen_j, j_c, ⟨⟩⟩ mj
                ⟨mrk_j, ws1_j, hj_le, hq_le_j, hql_j, heq_j, hqj, hcov_j, hmj⟩ ihj
              fvt_step; fvt_step
              · have hj_lt : j_c.toNat < rsz_bv.toNat := by
                  simp at hc; simp only [hrsn_2_mod, hrsz_raw] at hc; exact hc
                have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by bv_omega
                have hlit_idx : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat =
                    rsn_bv.toNat + 3 + j_c.toNat := by bv_omega
                have hlit_ar : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat <
                    s.core.arena.length := by omega
                fvt_to_group
                · let ol_bv :=
                    s.core.arena[(rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat]'hlit_ar
                  let ov_bv := ol_bv >>> 1#32
                  have hol_raw : s.core.arena[rsn_bv.toNat + 3 + j_c.toNat]'(by omega) = ol_bv := by
                    dsimp only [ol_bv]; simp only [hlit_idx]
                  have hol_mem : ol_bv.toNat ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat :=
                    (mem_fullArenaClauseLitsCore_iff hbd_r).mpr
                      ⟨j_c.toNat, by rw [← hrsz_eq]; exact hj_lt, congrArg BitVec.toNat hol_raw⟩
                  have hol_lt : ol_bv.toNat < 2 * s.core.cur_vars :=
                    hw.arena.lits_lt rsn_bv.toNat href_r hng_r ol_bv.toNat hol_mem
                  have hov_val : ov_bv.toNat = ol_bv.toNat / 2 := bv32_lshr1_toNat _
                  have hov_cv : ov_bv.toNat < s.core.cur_vars := by rw [hov_val]; omega
                  refine wp_join_group (ts := [i64])
                    (fun (qlen', ()) ml => ∃ (mrk_l : List (BitVec 8)) (ws1_l : List (BitVec 32)),
                      qlen_j.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
                      (∀ k < qlen_j.toNat, ws1_l[k]? = ws1_j[k]?) ∧
                      VivQueueOk c s mrk_l ws1_l qlen'.toNat ∧
                      (ov_bv.toNat ≠ v_bv.toNat →
                        (s.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
                        ov_bv.toNat ∈ (ws1_l.take qlen'.toNat).map BitVec.toNat) ∧
                      (FullMem c { s with
                        core := { s.core with mrk := mrk_l, lit_mark := lm1 }
                        scratch := { s.scratch with
                          work_stk1 := ws1_l, work_stk2 := ws2_b,
                          ant_sz := asz_1, res_sz := rsz_1 } } ⋆ R) ml)
                    (fun _ ⟨qlen', ⟨⟩⟩ ml
                        ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok, hcov_ov, hml⟩ => by
                      fvt_steps
                      have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
                      refine ihj (qlen', j_c + 1#32, ()) ml (by dsimp only; omega)
                        ⟨mrk_l, ws1_l, by omega, by omega, hql_l,
                         fun k hk => (heq_l k (by omega)).trans (heq_j k hk), hql_ok,
                         fun t ht hne => ?_, hml⟩
                      rcases (by omega : t < j_c.toNat ∨ t = j_c.toNat) with ht' | rfl
                      · refine (hcov_j t ht' hne).elim Or.inl fun hm' => Or.inr ?_
                        obtain ⟨k, hk, hkeq⟩ :=
                          (mem_map_take_iff (by have := hqj.2.1; omega)).mp hm'
                        exact (mem_map_take_iff (by omega)).mpr
                          ⟨k, by omega, by rw [heq_l k hk, hkeq]⟩
                      · have hleq :
                            (s.core.arena[rsn_bv.toNat + 3 + j_c.toNat]?.getD 0#32).toNat / 2 =
                            ov_bv.toNat := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                            hol_raw, hov_val]
                        rw [hleq] at hne ⊢; exact hcov_ov hne)
                    (fun Jl hJl => by
                      fvt_step; rw [wp_jnz]; constructor <;> intro hc
                      · have hne_bv : ov_bv ≠ v_bv := by
                          simp only [Arg.val_var, bne_iff_ne] at hc; exact hc
                        have hov_ne : ov_bv.toNat ≠ v_bv.toNat :=
                          fun he => hne_bv (BitVec.eq_of_toNat_eq he)
                        have hov_trl : ∃ m < s.core.trail_end,
                            (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat := by
                          rcases hlits_r ol_bv.toNat hol_mem with hsame | ⟨m, hm_lt, hmeq, _⟩
                          · exfalso; exact hov_ne (by rw [hov_val, hsame, htrl0])
                          · exact ⟨m, by omega, by rw [hmeq, fullInv_var_xor1, hov_val]⟩
                        exact m6_push_branch_step hspW.1 hqj hov_cv hov_trl hmj
                          fun qlen' mrk_l ws1_l ml hq_jl hql_l heq_l hql_ok hcov_ov hml =>
                            hJl (qlen', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok,
                              fun _ => hcov_ov, hml⟩
                      · have heq_bv : ov_bv = v_bv := by
                          simp only [Arg.val_var, bne_eq_false_iff_eq] at hc; exact hc
                        fvt_steps
                        exact hJl (qlen_j, ()) mj ⟨mrk_j, ws1_j, Nat.le_refl _, hql_j,
                          fun _ _ => rfl, hqj,
                          fun hne => absurd (congrArg BitVec.toNat heq_bv) hne, hmj⟩)
                · have hlt :
                      s.core.arena_len % 18446744073709551616 <
                        (rsn_bv.toNat + 3 + rsz_bv.toNat) % 18446744073709551616 := by
                    simp at hc; simp only [hrsn_2_mod, hrsz_raw] at hc; exact hc
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
                  have : rsn_bv.toNat + 3 + rsz_bv.toNat ≤ s.core.arena_len := by omega
                  omega
              · have hj_eq : j_c.toNat = rsz_bv.toNat := by
                  simp at hc; simp only [hrsn_2_mod, hrsz_raw] at hc
                  exact Nat.le_antisymm hj_le hc
                have hcov_l : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
                    q / 2 ≠ v_bv.toNat →
                    (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                    q / 2 ∈ (ws1_j.take qlen_j.toNat).map BitVec.toNat := by
                  intro q hq hne
                  obtain ⟨t, ht, hqt⟩ := (mem_fullArenaClauseLitsCore_iff hbd_r).mp hq
                  have ht_lt : rsn_bv.toNat + 3 + t < s.core.arena.length := by omega
                  rw [← hrsz_eq] at ht
                  have hc' := hcov_j t (by omega)
                    (by rw [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt]; exact hne)
                  rwa [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt] at hc'
                exact hJ qlen_j mrk_j ws1_j asz_1 rsz_1 mj hq_le_j hql_j heq_j hqj hsub_1
                  hcov_l hmj)
          (fun Jas hJas => by
            fvt_steps
            · c0_call hSubCl
              refine ⟨c, F0, F_cur, _, R, rfl,
                m6_deduce_state_len hspW.1 hqb.1 hlm1_len hqb.2.1 hws2_b,
                m6_deduce_state_witness hw, href_r, hng_r, hm_rs, fun ok => ?_⟩
              fvt_steps
              · exact hJas () _ ⟨rsn_bv.setWidth 64, m6_subRef_set_ref href_r, hm⟩
              · exact hJas () m_rs ⟨asz_b, hsub_b, hm_rs⟩
            · exact hJas () m_rs ⟨asz_b, hsub_b, hm_rs⟩
            · exact hJas () m_rs ⟨asz_b, hsub_b, hm_rs⟩))
      (fun Jrs hJrs => by
        fvt_steps
        · exact hJrs () _ ⟨1#64, hm⟩
        · exact hJrs () m ⟨rsz_b, hm⟩)

private abbrev m6DeducePhase2Expr
    (h pVars pMark pLitMark pTmp pLevel pRsns pArena pWs1 pWs2 : Val i64)
    (cref sz implied : Val i32) (qlen : Val i64) (olen : Val i32) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 96, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTrl =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 360, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTpos =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun Js => Blocks.cons (fun p_17 =>
    fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
      (Arg.var p_17.snd.fst, Arg.var p_17.fst, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.mul i64) (Arg.var p_17.snd.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun v_bv =>
       fvOp32 (OpCode.add i64) (Arg.var p_17.snd.fst, Arg.imm 1, ()) fun p_qi1 =>
       fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
       fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pRsns, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun rsn_bv =>
       Expr.group (sig := [[i64, i32, .bool]]) (fun _ => Blocks.cons (fun p =>
         Expr.jump Js.fst (Arg.var p.fst, Arg.var p_qi1.fst, Arg.var p.snd.fst,
           Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Js_r =>
       fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
         (Arg.var rsn_bv, Arg.imm 4294967295, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun tp =>
          fvOp32 (OpCode.zext 32 64) (Arg.var tp, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun tl =>
          Expr.group (sig := [[i32, .bool]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump Js_r.fst (Arg.var p_17.fst, Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
            fun Js_d =>
          fvOp32 (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var tl, Arg.var implied, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.jump Js_d.fst (Arg.var p_17.snd.snd.fst, Arg.imm (t := .bool) true, ()))
            (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p =>
              Expr.jump Js_d.fst (Arg.var p.fst, Arg.var p_17.snd.snd.snd.fst, ())) Blocks.nil)
              fun Js_o =>
             fvOp32 (OpCode.zext 32 64) (Arg.var p_17.snd.snd.fst, ()) fun po =>
             fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
               (Arg.var po.fst, Arg.var pVars, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp32 (OpCode.zext 32 64) (Arg.var p_17.snd.snd.fst, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pWs2, Arg.var p.fst, ()) fun p =>
                fvOp32 (OpCode.xor i32) (Arg.var tl, Arg.imm 1, ()) fun px =>
                Expr.store (Arg.var px.fst) (Arg.var p.fst)
                  (fvOp32 (OpCode.add i32) (Arg.var p_17.snd.snd.fst, Arg.imm 1, ()) fun p =>
                   Expr.jump Js_o.fst (Arg.var p.fst, ())))
               (Expr.jump Js_o.fst (Arg.var p_17.snd.snd.fst, ()))))
         (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump Js_r.fst (Arg.var p.fst, Arg.var p_17.snd.snd.fst,
              Arg.var p_17.snd.snd.snd.fst, ())) Blocks.nil) fun Js_g =>
          fvOp32 (OpCode.and i32) (Arg.var rsn_bv, Arg.imm 2147483648, ()) fun p =>
          fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.and i32) (Arg.var rsn_bv, Arg.imm 2147483647, ()) fun p_ot =>
             Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
               fvOp32 (OpCode.lshr i32) (Arg.var p_ot.fst, Arg.imm 1, ()) fun p_ov =>
               Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                 Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_b =>
               deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_17.fst Js_b.fst) Blocks.nil)
               fun Js_sb =>
             fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.load i64 (Arg.var p.fst) fun ld =>
             fvOp32 (OpCode.cmp .eq i64 .bool (by decide))
               (Arg.var ld, Arg.imm 18446744073709551615, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun tp =>
                fvOp32 (OpCode.zext 32 64) (Arg.var tp, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun tl =>
                Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
                  Expr.jump Js_sb.fst ()) Blocks.nil) fun Js_sb2 =>
                Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
                  (Arg.var h, Arg.var tl, Arg.var p_ot.fst, ()) fun ok =>
                Expr.jnz (Arg.var ok.fst)
                  (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
                   Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst)
                     (Expr.jump Js_sb2.fst ()))
                  (Expr.jump Js_sb2.fst ()))
               (Expr.jump Js_sb.fst ()))
            (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
               Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_lg =>
             m6DeduceLargeRsnExpr h pVars pMark pLevel pArena pWs1 cref sz rsn_bv v_bv
               p_17.fst Js_lg.fst)))
      (m6DeduceClearExpr h pMark pLitMark pTmp pWs1 sz p_17.fst p_17.snd.snd.fst
        p_17.snd.snd.snd.fst)) Blocks.nil)
    fun Js => Expr.jump Js.fst
      (Arg.var qlen, Arg.imm 0, Arg.var olen, Arg.imm (t := .bool) false, ())

private theorem m6_deduce_phase2_wp (Γ : Env)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk1 lm1 : List (BitVec 8)} {ws1_1 ws2_1 : List (BitVec 32)} {asz1 rsz1 : BitVec 64}
    {qlen_v : Val i64} {cref sz implied olen_v : Val i32} {mp : Mem 64}
    {Q : Post [i32]} {X : XPost}
    (hspW : FullSparseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_1 : ws2_1.length = 2 * c.max_vars) (hql1 : qlen_v.toNat ≤ s.core.cur_vars)
    (hq1 : VivQueueOk c s mrk1 ws1_1 qlen_v.toNat)
    (ho1 : VivOutOk s implied ws1_1 ws2_1 0 olen_v.toNat false)
    (hsd1 : VivSeedOk s cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false)
    (hsub1 : M6SubRefOk s asz1)
    (hsdi1 : implied ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat)
    (hmp : (FullMem c { s with
      core := { s.core with mrk := mrk1, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_1, work_stk2 := ws2_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) mp)
    (hQ : ∀ olen mrk' lm' ws1' ws2' asz' rsz' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → M6SubRefOk s asz' →
      (olen ≠ 0xFFFFFFFF#32 →
        olen.toNat ≤ s.core.cur_vars ∧
        (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (olen, ()) m') :
    wp Γ Q X (m6DeducePhase2Expr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLitMark c.pTmp c.pLevel c.pReason c.pArena c.pWorkStk1 c.pWorkStk2
      cref sz implied qlen_v olen_v) mp := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have hrsns_len := hcl.rsns_len; have htrl_len := hcl.trl_len; have htp_len := hcl.trail_pos_len
  dsimp only [m6DeducePhase2Expr, fvOp32]
  fvt_to_group
  refine wp_loop_inv (ts := [i64, i64, i32, .bool])
    (fun (qlen_c, qi_c, olen_c, taut_c, ()) mb =>
      ∃ (mrk_b : List (BitVec 8)) (ws1_b ws2_b : List (BitVec 32)) (asz_b rsz_b : BitVec 64),
        ws2_b.length = 2 * c.max_vars ∧ qi_c.toNat ≤ qlen_c.toNat ∧ qlen_c.toNat ≤ s.core.cur_vars ∧
        VivQueueOk c s mrk_b ws1_b qlen_c.toNat ∧
        VivClosedOk s implied ws1_b ws2_b qi_c.toNat qlen_c.toNat olen_c.toNat taut_c ∧
        VivOutOk s implied ws1_b ws2_b qi_c.toNat olen_c.toNat taut_c ∧
        VivSeedOk s cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat taut_c ∧
        M6SubRefOk s asz_b ∧
        (implied ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ (ws1_b.take qlen_c.toNat).map BitVec.toNat) ∧
        (FullMem c { s with
          core := { s.core with mrk := mrk_b, lit_mark := lm1 }
          scratch := { s.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mb)
    (fun (_, qi_c, _, _, ()) _ => s.core.cur_vars - qi_c.toNat) ?_ ?_
  · intro Jb hJb; fvt_steps
    exact hJb (qlen_v, 0#64, olen_v, false, ()) mp
      ⟨mrk1, ws1_1, ws2_1, asz1, rsz1, hws2_1, by simp, hql1, hq1,
       (fun _ h => absurd h (Nat.not_lt_zero _)), ho1, hsd1, hsub1, hsdi1, hmp⟩
  · rintro Jb ⟨qlen_c, qi_c, olen_c, taut_c, ⟨⟩⟩ mb
      ⟨mrk_b, ws1_b, ws2_b, asz_b, rsz_b, hws2_b, hqi_le, hql_le, hqb, hcb, hob,
       hsdb, hsub_b, hsdi_b, hmb⟩ ihb
    fvt_step; fvt_step
    · have hqi_lt : qi_c.toNat < qlen_c.toNat := by c0_bound
      have hqi1 : (qi_c + 1#64).toNat = qi_c.toNat + 1 := by bv_omega
      have hqi_ws1 : qi_c.toNat < ws1_b.length := by have := hqb.2.1; omega
      let v_bv := ws1_b[qi_c.toNat]'hqi_ws1
      have hv_lt : v_bv.toNat < s.core.cur_vars := by
        have := hqb.2.2.2.1 qi_c.toNat hqi_lt
        rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some] at this
      have hv_rsn : v_bv.toNat < s.core.rsns.length := by omega
      have hv_tp : v_bv.toNat < s.core.trail_pos.length := by omega
      have hv_lvl : 0 < (s.core.lvl[v_bv.toNat]?.getD 0#32).toNat ∧
          ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = v_bv.toNat := by
        have := hqb.2.2.2.2.2.1 qi_c.toNat hqi_lt
        rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some] at this
      obtain ⟨idx0, hidx0, htrl0⟩ := hv_lvl.2
      have htp_eq : (s.core.trail_pos[v_bv.toNat]'hv_tp).toNat = idx0 := by
        have h := hw.trail_pos_inv idx0 hidx0
        rw [htrl0, List.getElem?_eq_getElem hv_tp, Option.getD_some] at h; exact h
      have htp_trl : (s.core.trail_pos[v_bv.toNat]'hv_tp).toNat < s.core.trl.length := by omega
      fvt_to_group
      refine wp_join_group (ts := [i64, i32, .bool])
        (fun (qlen', olen', taut', ()) mn =>
          ∃ (mrk_n : List (BitVec 8)) (ws1_n ws2_n : List (BitVec 32)) (asz_n rsz_n : BitVec 64),
            ws2_n.length = 2 * c.max_vars ∧ qi_c.toNat + 1 ≤ qlen'.toNat ∧
            qlen'.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_n ws1_n qlen'.toNat ∧
            VivClosedOk s implied ws1_n ws2_n (qi_c.toNat + 1) qlen'.toNat olen'.toNat taut' ∧
            VivOutOk s implied ws1_n ws2_n (qi_c.toNat + 1) olen'.toNat taut' ∧
            VivSeedOk s cref implied ws1_n ws2_n qlen'.toNat olen'.toNat taut' ∧
            M6SubRefOk s asz_n ∧
            (implied ≠ 0xFFFFFFFF#32 →
              (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_n, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_n, work_stk2 := ws2_n, ant_sz := asz_n, res_sz := rsz_n } }
              ⋆ R) mn)
        (fun _ ⟨qlen', olen', taut', ⟨⟩⟩ mn
            ⟨mrk_n, ws1_n, ws2_n, asz_n, rsz_n, hws2_n, hqi1_le, hql_n, hqn, hcn, hon,
             hsdn, hsub_n, hsdin, hmn⟩ => by
          fvt_steps
          exact ihb (qlen', qi_c + 1#64, olen', taut', ()) mn (by dsimp only; omega)
            ⟨mrk_n, ws1_n, ws2_n, asz_n, rsz_n, hws2_n, by omega, hql_n, hqn, by rwa [hqi1],
             by rwa [hqi1], hsdn, hsub_n, hsdin, hmn⟩)
        (fun Jn hJn => ?_)
      fvt_to_group
      · -- Decision: `rsn == 0xFFFFFFFFu`
        have hrsn_ff : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem hv_rsn, Option.getD_some]; c0_bound
        let tl_bv := s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl
        have htl_get : s.core.trl[idx0]?.getD 0#32 = tl_bv := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          dsimp only [tl_bv]; simp only [htp_eq]
        have htl_lt : tl_bv.toNat < 2 * s.core.cur_vars := by
          have := hw.trail_lits_lt idx0 hidx0; rwa [htl_get] at this
        have htrl0' : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
            (ws1_b[qi_c.toNat]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]; exact htrl0
        have hrsn_ff' : s.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            0xFFFFFFFF#32 := by
          rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
        refine wp_join_group (ts := [i32, .bool])
          (fun (olen', taut', ()) md => ∃ ws2_d : List (BitVec 32), ws2_d.length = 2 * c.max_vars ∧
            VivClosedOk s implied ws1_b ws2_d (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut' ∧
            VivOutOk s implied ws1_b ws2_d (qi_c.toNat + 1) olen'.toNat taut' ∧
            VivSeedOk s cref implied ws1_b ws2_d qlen_c.toNat olen'.toNat taut' ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_b, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_d, ant_sz := asz_b, res_sz := rsz_b } }
              ⋆ R) md)
          (fun _ ⟨olen', taut', ⟨⟩⟩ md ⟨ws2_d, hws2_d, hcd, hod, hsdd, hmd⟩ => by
            fvt_steps
            exact hJn (qlen_c, olen', taut', ()) md
              ⟨mrk_b, ws1_b, ws2_d, asz_b, rsz_b, hws2_d, by omega, hql_le, hqb, hcd, hod, hsdd,
               hsub_b, hsdi_b, hmd⟩)
          (fun Jd hJd => ?_)
        fvt_to_group
        · exact hJd (olen_c, true, ()) mb ⟨ws2_b, hws2_b,
            m6_vivClosed_taut_true hcb hrsn_ff', (fun h => by cases h),
            (fun h => by cases h), hmb⟩
        · have htl_ne : tl_bv ≠ implied := by c0_bound
          refine wp_join_group (ts := [i32])
            (fun (olen', ()) mo => ∃ ws2_o : List (BitVec 32), ws2_o.length = 2 * c.max_vars ∧
              VivClosedOk s implied ws1_b ws2_o (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut_c ∧
              VivOutOk s implied ws1_b ws2_o (qi_c.toNat + 1) olen'.toNat taut_c ∧
              VivSeedOk s cref implied ws1_b ws2_o qlen_c.toNat olen'.toNat taut_c ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_b, work_stk2 := ws2_o, ant_sz := asz_b, res_sz := rsz_b } }
                ⋆ R) mo)
            (fun _ ⟨olen', ⟨⟩⟩ mo ⟨ws2_o, hws2_o, hco, hoo, hsdo, hmo⟩ =>
              hJd (olen', taut_c, ()) mo ⟨ws2_o, hws2_o, hco, hoo, hsdo, hmo⟩)
            (fun Jo hJo => by
              fvt_steps
              · have hol_lt : olen_c.toNat < s.core.cur_vars := by
                  have hlt : olen_c.toNat < s.core.cur_vars % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at hlt
                have hol_ws2 : olen_c.toNat < ws2_b.length := by omega
                have hol1 : (olen_c + 1#32).toNat = olen_c.toNat + 1 := by bv_omega
                let ws2_o := ws2_b.set olen_c.toNat (tl_bv ^^^ 1#32)
                have hws2_o_len : ws2_o.length = 2 * c.max_vars := by simp [ws2_o, hws2_b]
                cases taut_c with
                | true =>
                  exact hJo (olen_c + 1#32, ()) _ ⟨ws2_o, hws2_o_len,
                    m6_vivClosed_taut_true hcb hrsn_ff', (fun h => by cases h),
                    (fun h => by cases h), by assumption⟩
                | false =>
                  have hpush := vivOut_push_step hw hqb hqi_lt hob hcb himp
                    hidx0 htrl0' hrsn_ff' (fun _ => htl_get.symm ▸ htl_ne) hws2_b hcv_le
                  have hws2_o_eq : ws2_o = ws2_b.set olen_c.toNat
                      ((s.core.trl[idx0]?.getD 0#32) ^^^ 1#32) := by
                    dsimp only [ws2_o]; rw [htl_get]
                  have hco : VivClosedOk s implied ws1_b ws2_o (qi_c.toNat + 1) qlen_c.toNat
                      (olen_c + 1#32).toNat false := by
                    rw [hol1, hws2_o_eq]; exact hpush.2.2.2.1
                  have hoo : VivOutOk s implied ws1_b ws2_o (qi_c.toNat + 1)
                      (olen_c + 1#32).toNat false := by
                    rw [hol1, hws2_o_eq]; exact hpush.2.2.1
                  have hsdo : VivSeedOk s cref implied ws1_b ws2_o qlen_c.toNat
                      (olen_c + 1#32).toNat false := by
                    rw [hol1]
                    exact m6_vivSeed_mono_ws2 hsdb (by omega) (by omega)
                      (by omega) (fun j hj => by rw [hws2_o_eq]; exact hpush.2.2.2.2 j hj)
                  exact hJo (olen_c + 1#32, ()) _ ⟨ws2_o, hws2_o_len, hco, hoo, hsdo,
                    by assumption⟩
              · cases taut_c with
                | true =>
                  exact hJo (olen_c, ()) mb ⟨ws2_b, hws2_b,
                    m6_vivClosed_taut_true hcb hrsn_ff', (fun h => by cases h),
                    (fun h => by cases h), hmb⟩
                | false =>
                  have hol_lt_cv := (vivOut_push_lt hw hqb hcv_le hqi_lt hob himp
                    hidx0 htrl0' (fun _ => htl_get.symm ▸ htl_ne)
                    (by have := hob rfl; omega)).1
                  have hcv_le_o : s.core.cur_vars % 2 ^ 64 ≤ olen_c.toNat := by c0_bound
                  rw [Nat.mod_eq_of_lt (by omega)] at hcv_le_o; omega)
      · -- Non-decision reason (`rsn ≠ 0xFFFFFFFFu`)
        have hv_set64 : (v_bv.setWidth 64).toNat = v_bv.toNat := by bv_omega
        let rsn_bv := s.core.rsns[(v_bv.setWidth 64).toNat]'(by rw [hv_set64]; exact hv_rsn)
        have hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32 := by dsimp only [rsn_bv]; c0_bound
        have hrsn_get : s.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            rsn_bv := by
          dsimp only [rsn_bv, v_bv]
          rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some,
            List.getElem?_eq_getElem hv_rsn, Option.getD_some]
          congr 1
        have htrl0' : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
            (ws1_b[qi_c.toNat]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]; exact htrl0
        refine wp_join_group (ts := [i64])
          (fun (qlen', ()) mr => ∃ (mrk_r : List (BitVec 8)) (ws1_r : List (BitVec 32))
              (asz_r rsz_r : BitVec 64),
            qi_c.toNat + 1 ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
            VivQueueOk c s mrk_r ws1_r qlen'.toNat ∧
            VivClosedOk s implied ws1_r ws2_b (qi_c.toNat + 1) qlen'.toNat olen_c.toNat taut_c ∧
            VivOutOk s implied ws1_r ws2_b (qi_c.toNat + 1) olen_c.toNat taut_c ∧
            VivSeedOk s cref implied ws1_r ws2_b qlen'.toNat olen_c.toNat taut_c ∧
            M6SubRefOk s asz_r ∧
            (implied ≠ 0xFFFFFFFF#32 →
              (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_r.take qlen'.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_r, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_r, work_stk2 := ws2_b, ant_sz := asz_r, res_sz := rsz_r } }
              ⋆ R) mr)
          (fun _ ⟨qlen', ⟨⟩⟩ mr ⟨mrk_r, ws1_r, asz_r, rsz_r, hq1_r, hql_r, hqr, hcr, hor,
              hsdr, hsub_r, hsdir, hmr⟩ => by
            fvt_steps
            exact hJn (qlen', olen_c, taut_c, ()) mr
              ⟨mrk_r, ws1_r, ws2_b, asz_r, rsz_r, hws2_b, hq1_r, hql_r, hqr, hcr, hor,
               hsdr, hsub_r, hsdir, hmr⟩)
          (fun Jr hJr => ?_)
        fvt_to_group
        · -- Binary reason: `(rsn & PW_BIN_FLAG) != 0`
          have hbin : (rsn_bv &&& 0x80000000#32) ≠ 0#32 := by c0_bound
          have hri := hw.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
          rw [htrl0', hrsn_get, ite_eq_left hbin] at hri
          obtain ⟨hot_lt, _, m_bin, hm_lt_bin, hmeq_bin, _⟩ := hri
          let ot_bv := rsn_bv &&& 0x7FFFFFFF#32
          let ov_bv := ot_bv >>> 1#32
          have hov_val : ov_bv.toNat = ot_bv.toNat / 2 := bv32_lshr1_toNat _
          have hov_cv : ov_bv.toNat < s.core.cur_vars := by
            dsimp only [ot_bv] at hov_val; rw [hov_val]; omega
          have hov_trl : ∃ m < s.core.trail_end,
              (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat :=
            ⟨m_bin, by omega, by rw [hmeq_bin, fullInv_var_xor1, hov_val]⟩
          refine wp_join_group (ts := [])
            (fun _ m_sub => ∃ asz_s : BitVec 64, M6SubRefOk s asz_s ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_s, res_sz := rsz_b } }
                ⋆ R) m_sub)
            (fun _ _ m_sub ⟨asz_s, hsub_s, hm_sub⟩ => by
              fvt_to_group
              refine wp_join_group (ts := [i64])
                (fun (qlen', ()) mbin => ∃ (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)),
                  qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
                  (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) ∧
                  VivQueueOk c s mrk_n ws1_n qlen'.toNat ∧
                  ((s.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
                    ov_bv.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
                  (FullMem c { s with
                    core := { s.core with mrk := mrk_n, lit_mark := lm1 }
                    scratch := { s.scratch with
                      work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_s, res_sz := rsz_b } }
                    ⋆ R) mbin)
                (fun _ ⟨qlen', ⟨⟩⟩ mbin
                    ⟨mrk_n, ws1_n, hq_le, hql_n, heq_n, hqn, hcov_b, hmbin⟩ => by
                  fvt_steps
                  have hws1_n_len : ws1_n.length = 2 * c.max_vars := hqn.2.1
                  have heq_qi : ws1_n[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_n qi_c.toNat hqi_lt
                  have htrl0_n : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
                      (ws1_n[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
                  have hcb1 := vivClosed_mono_q hcb (by omega) hq_le
                    (by have := hqb.2.1; omega) (by omega) heq_n
                  have hcb2 := vivClosed_step_bin hcb1 hw.trail_vars_nodup hidx0 htrl0_n
                    (by rw [heq_qi, hrsn_get]; exact hrsn_ne) (by rw [heq_qi, hrsn_get]; exact hbin)
                    (by rw [heq_qi, hrsn_get, ← hov_val]; exact hcov_b)
                  have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
                    (by have := hqb.2.1; omega) (by omega) heq_n
                  have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega) (by omega)
                    (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
                  have hsd1 := vivSeed_mono_q hsdb hq_le (by omega)
                    (by have := hqb.2.1; omega) heq_n
                  have hsdi1 : implied ≠ 0xFFFFFFFF#32 →
                      (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                      implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat :=
                    fun hne => (hsdi_b hne).elim Or.inl fun hm' => Or.inr (by
                      obtain ⟨j, hj, hjeq⟩ := (mem_map_take_iff (by have := hqb.2.1; omega)).mp hm'
                      exact (mem_map_take_iff (by omega)).mpr
                        ⟨j, by omega, by rw [heq_n j hj, hjeq]⟩)
                  exact hJr (qlen', ()) mbin ⟨mrk_n, ws1_n, asz_s, rsz_b, by omega, hql_n, hqn,
                    hcb2, hob2, hsd1, hsub_s, hsdi1, hmbin⟩)
                (fun Jbin hJbin => m6_push_branch_step hspW.1 hqb hov_cv hov_trl hm_sub
                  fun qlen' mrk_n ws1_n mbin hq_le hql_n heq_n hqn hcov_b hmbin =>
                    hJbin (qlen', ()) mbin ⟨mrk_n, ws1_n, hq_le, hql_n, heq_n, hqn, hcov_b, hmbin⟩))
            (fun Js hJs => by
              fvt_to_group
              · refine wp_join_group (ts := [])
                  (fun _ m_sub => ∃ asz_s : BitVec 64, M6SubRefOk s asz_s ∧
                    (FullMem c { s with
                      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                      scratch := { s.scratch with
                        work_stk1 := ws1_b, work_stk2 := ws2_b,
                        ant_sz := asz_s, res_sz := rsz_b } } ⋆ R) m_sub)
                  (fun _ _ m_sub h => hJs () m_sub h)
                  (fun Js2 hJs2 => by
                    have htl_lt :
                        (s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl).toNat <
                          2 * s.core.cur_vars := by
                      have h := hw.trail_lits_lt idx0 hidx0
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
                      simpa only [htp_eq] using h
                    fvt_steps; c0_call hSubBin
                    refine ⟨c, _, R, rfl,
                      m6_deduce_state_len hspW.1 hqb.1 hlm1_len hqb.2.1 hws2_b,
                      htl_lt, hot_lt, hmb, fun ok => ?_⟩
                    fvt_steps
                    · exact hJs2 () _ ⟨0xFFFFFFFFFFFFFFFE#64, Or.inr (Or.inl rfl), hm⟩
                    · exact hJs2 () mb ⟨asz_b, hsub_b, hmb⟩)
              · exact hJs () mb ⟨asz_b, hsub_b, hmb⟩)
        · -- Large reason: `(rsn & PW_BIN_FLAG) == 0`
          have hlg : (rsn_bv &&& 0x80000000#32) = 0#32 := by c0_bound
          have hri := hw.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
          rw [htrl0', hrsn_get, ite_eq_right (by simp [hlg])] at hri
          obtain ⟨href_r, hng_r, hlits_r⟩ := hri
          have hv_get : v_bv = ws1_b[qi_c.toNat]?.getD 0#32 := by
            dsimp only [v_bv]; rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
          refine wp_join_group (ts := [i64])
            (fun (qlen', ()) mlg => ∃ (mrk_l : List (BitVec 8)) (ws1_l : List (BitVec 32))
                (asz_l rsz_l : BitVec 64),
              qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
              (∀ j < qlen_c.toNat, ws1_l[j]? = ws1_b[j]?) ∧
              VivQueueOk c s mrk_l ws1_l qlen'.toNat ∧ M6SubRefOk s asz_l ∧
              (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
                (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                q / 2 ∈ (ws1_l.take qlen'.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_l, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_l, work_stk2 := ws2_b, ant_sz := asz_l, res_sz := rsz_l } }
                ⋆ R) mlg)
            (fun _ ⟨qlen', ⟨⟩⟩ mlg
                ⟨mrk_l, ws1_l, asz_l, rsz_l, hq_le_l, hql_l, heq_l, hql_ok, hsub_l, hcov_l,
                 hmlg⟩ => by
              fvt_steps
              have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
              have heq_qi : ws1_l[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_l qi_c.toNat hqi_lt
              have htrl0_n : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
                  (ws1_l[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
              have hcb1 := vivClosed_mono_q hcb (by omega) hq_le_l
                (by have := hqb.2.1; omega) (by omega) heq_l
              have hcb2 := vivClosed_step_large hcb1 hw.trail_vars_nodup hidx0 htrl0_n
                (by rw [heq_qi, hrsn_get]; exact hrsn_ne) (by rw [heq_qi, hrsn_get]; exact hlg)
                (by rw [heq_qi, hrsn_get, ← hv_get]; exact hcov_l)
                (by rw [heq_qi, hrsn_get]; intro q hq
                    exact (hlits_r q hq).imp id fun ⟨m, hm', heq, _⟩ => ⟨m, hm', heq⟩)
              have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
                (by have := hqb.2.1; omega) (by omega) heq_l
              have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega) (by omega)
                (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
              have hsd1 := vivSeed_mono_q hsdb hq_le_l (by omega)
                (by have := hqb.2.1; omega) heq_l
              have hsdi1 : implied ≠ 0xFFFFFFFF#32 →
                  (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                  implied.toNat / 2 ∈ (ws1_l.take qlen'.toNat).map BitVec.toNat :=
                fun hne => (hsdi_b hne).elim Or.inl fun hm' => Or.inr (by
                  obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by have := hqb.2.1; omega)).mp hm'
                  exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq_l k hk, hkeq]⟩)
              exact hJr (qlen', ()) mlg ⟨mrk_l, ws1_l, asz_l, rsz_l, by omega, hql_l, hql_ok,
                hcb2, hob2, hsd1, hsub_l, hsdi1, hmlg⟩)
            (fun Jlg hJlg => m6_deduce_large_rsn_wp Γ hSubCl hspW hqb hlm1_len hws2_b hsub_b
              href_r hng_r hidx0 htrl0 (fun q hq => by rw [htrl0']; exact hlits_r q hq) hmb
              fun qlen' mrk_l ws1_l asz_l rsz_l mlg h1 h2 h3 h4 h5 h6 h7 =>
                hJlg (qlen', ()) mlg ⟨mrk_l, ws1_l, asz_l, rsz_l, h1, h2, h3, h4, h5, h6, h7⟩)
    · -- Phase 2 loop exit (`qi == qlen`): call `m6_deduce_clear_wp`
      have hqi_eq : qi_c.toNat = qlen_c.toNat := by c0_bound
      refine m6_deduce_clear_wp Γ hspW hsz_le htmp_lt hqb hlm1_len hlm1_dom hws2_b hsub_b hmb
        fun ret mrk' lm' asz' mf hsp' hsub' ht_eq hf_eq hmf => ?_
      refine hQ ret mrk' lm' ws1_b ws2_b asz' rsz_b mf hsp' hsub' (fun hne_ff => ?_) hmf
      have htf : taut_c = false := by
        cases htc : taut_c with
        | false => rfl
        | true => exact absurd (ht_eq htc) hne_ff
      have hret_eq : ret = olen_c := hf_eq htf
      rw [hret_eq]
      have hcb' :
          VivClosedOk s implied ws1_b ws2_b qlen_c.toNat qlen_c.toNat olen_c.toNat false := by
        rw [hqi_eq, htf] at hcb; exact hcb
      have hob' : VivOutOk s implied ws1_b ws2_b qlen_c.toNat olen_c.toNat false := by
        rw [hqi_eq, htf] at hob; exact hob
      have hsdb' : VivSeedOk s cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat false := by
        rw [htf] at hsdb; exact hsdb
      have hent_out :=
        deduce_phase2_sound hw hqb hcv_le href hng hcb' hsdb' himp hconfl hsdi_b
      have hsub_o := hob' rfl
      refine ⟨hsub_o.1, hsub_o.2.1,
        by simpa only [List.map_map, Function.comp_def] using hsub_o.2.2.1, hent_out⟩

private abbrev m6DeducePhase1bBinExpr (h pVars pMark pLevel pWs1 : Val i64) (J : Cont [i64]) :
    Expr Val Cont [i32] :=
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 536, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld =>
  fvOp32 (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_19 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 544, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld =>
  fvOp32 (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_21 =>
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
    Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
        Expr.jump J (Arg.var p.fst, ())) Blocks.nil) fun Js =>
      fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_22 =>
      fvOp32 (OpCode.zext 32 64) (Arg.var p_22.fst, ()) fun p_23 =>
      fvOp32 (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()) fun p_24 =>
      fvOp32 (OpCode.add i64) (Arg.var pLevel, Arg.var p_24.fst, ()) fun p_25 =>
      Expr.load i32 (Arg.var p_25.fst) fun ld =>
      fvOp32 (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p_26 =>
      Expr.jnz (Arg.var p_26.fst)
        (fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_27 =>
         fvOp32 (OpCode.zext 32 64) (Arg.var p_27.fst, ()) fun p_28 =>
         fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p_28.fst, ()) fun p_29 =>
         Expr.load i8 (Arg.var p_29.fst) fun ld =>
         fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p_30 =>
         fvOp32 (OpCode.zext 8 32) (Arg.var ld, ()) fun p_31 =>
         fvOp32 (OpCode.zext 8 32) (Arg.var p_30.fst, ()) fun p_32 =>
         fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
           (Arg.var p_31.fst, Arg.var p_32.fst, ()) fun p_33 =>
         Expr.jnz (Arg.var p_33.fst)
           (fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
              (Arg.var p.fst, Arg.var pVars, ()) fun p_34 =>
            Expr.jnz (Arg.var p_34.fst)
              (fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_35 =>
               fvOp32 (OpCode.zext 32 64) (Arg.var p_35.fst, ()) fun p_36 =>
               fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p_36.fst, ()) fun p_37 =>
               fvOp32 (OpCode.trunc 32 8) (Arg.imm 1, ()) fun p_38 =>
               Expr.store (Arg.var p_38.fst) (Arg.var p_37.fst)
                 (fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p_39 =>
                  fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p_39.fst, ()) fun p_40 =>
                  fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_41 =>
                  Expr.store (Arg.var p_41.fst) (Arg.var p_40.fst)
                    (fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
                     Expr.jump Js.fst (Arg.var p.fst, ()))))
              (Expr.jump Js.fst (Arg.var p.fst, ())))
           (Expr.jump Js.fst (Arg.var p.fst, ())))
        (Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil) fun Js =>
    fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
    fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
    fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
    fvOp32 (OpCode.add i64) (Arg.var pLevel, Arg.var p.fst, ()) fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld =>
    fvOp32 (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
       fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
       Expr.load i8 (Arg.var p.fst) fun ld =>
       fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p =>
       fvOp32 (OpCode.zext 8 32) (Arg.var ld, ()) fun p_22 =>
       fvOp32 (OpCode.zext 8 32) (Arg.var p.fst, ()) fun p =>
       fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
         (Arg.var p_22.fst, Arg.var p.fst, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
            (Arg.imm 0, Arg.var pVars, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
             fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
             fvOp32 (OpCode.trunc 32 8) (Arg.imm 1, ()) fun p_23 =>
             Expr.store (Arg.var p_23.fst) (Arg.var p.fst)
               (fvOp32 (OpCode.mul i64) (Arg.imm 0, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
                fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p_24 =>
                Expr.store (Arg.var p_24.fst) (Arg.var p.fst)
                  (fvOp32 (OpCode.add i64) (Arg.imm 0, Arg.imm 1, ()) fun p =>
                   Expr.jump Js.fst (Arg.var p.fst, ()))))
            (Expr.jump Js.fst (Arg.imm 0, ())))
         (Expr.jump Js.fst (Arg.imm 0, ())))
      (Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil) fun Js =>
  Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var p_19.fst, Arg.var p_21.fst, ()) fun p_22 =>
  Expr.jnz (Arg.var p_22.fst)
    (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst) (Expr.jump Js.fst ()))
    (Expr.jump Js.fst ())

private theorem m6_deduce_phase1b_bin_wp (Γ : Env)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {cref implied : Val i32} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    {Jq : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (himp_eq : implied = 0xFFFFFFFF#32)
    (hct1 : s.core.confl_type = 1#64)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hm : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m)
    (hJq : ∀ (qlen_v : Val i64) (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
        (asz1 rsz1 : BitVec 64) m_q,
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s mrk1 ws1_1 qlen_v.toNat →
      VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false →
      M6SubRefOk s asz1 →
      (FullMem c { s with
        core := { s.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) m_q →
      Jq (qlen_v, ()) m_q) :
    wp Γ Q X (m6DeducePhase1bBinExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 Jq) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hmrk_len := hcl.mrk_len
  have hlvl_len := hcl.lvl_len; have hws1_len := hscl.work_stk1_len
  have hws2_len := hscl.work_stk2_len
  rcases hconfl himp_eq with (⟨_, ha_lt, hb_lt, _, hva, hvb⟩ | ⟨hct2, _⟩) | ⟨hct0, _⟩
  · have ha32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have hb32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a_bv := s.core.confl_lit0.truncate 32
    let b_bv := s.core.confl_lit1.truncate 32
    have ha_eq : a_bv.toNat = s.core.confl_lit0.toNat := bv64_trunc32_toNat ha32
    have hb_eq : b_bv.toNat = s.core.confl_lit1.toNat := bv64_trunc32_toNat hb32
    have hav_cv : (a_bv >>> 1#32).toNat < s.core.cur_vars := by
      rw [bv32_lshr1_toNat, ha_eq]; omega
    have hbv_cv : (b_bv >>> 1#32).toNat < s.core.cur_vars := by
      rw [bv32_lshr1_toNat, hb_eq]; omega
    have ha_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = (a_bv >>> 1#32).toNat := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, bv32_lshr1_toNat, ha_eq]⟩
    have hb_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = (b_bv >>> 1#32).toNat := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, bv32_lshr1_toNat, hb_eq]⟩
    dsimp only [m6DeducePhase1bBinExpr, fvOp32]
    fvt_to_group
    refine wp_join_group (ts := [])
      (fun _ m_sb => ∃ asz1 : BitVec 64, M6SubRefOk s asz1 ∧
        (FullMem c { s with
          core := { s.core with lit_mark := lm1 }
          scratch := { s.scratch with ant_sz := asz1, res_sz := 0#64 } } ⋆ R) m_sb)
      (fun _ _ m_sb ⟨asz1, hsub1, hm_sb⟩ => by
        fvt_to_group
        refine wp_join_group (ts := [i64])
          (fun (qa, ()) ma => ∃ (mrk_a : List (BitVec 8)) (ws1_a : List (BitVec 32)),
            qa.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_a ws1_a qa.toNat ∧
            ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
              s.core.confl_lit0.toNat / 2 ∈ (ws1_a.take qa.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_a, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_a, ant_sz := asz1, res_sz := 0#64 } } ⋆ R) ma)
          (fun _ ⟨qa, ⟨⟩⟩ ma ⟨mrk_a, ws1_a, hqa_le, hqa, hcov_a, hma⟩ => by
            fvt_to_group
            refine wp_join_group (ts := [i64])
              (fun (qb, ()) mb =>
                ∃ (mrk_b : List (BitVec 8)) (ws1_b : List (BitVec 32)),
                  qa.toNat ≤ qb.toNat ∧ qb.toNat ≤ s.core.cur_vars ∧
                  (∀ j < qa.toNat, ws1_b[j]? = ws1_a[j]?) ∧
                  VivQueueOk c s mrk_b ws1_b qb.toNat ∧
                  ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = 0 ∨
                    s.core.confl_lit1.toNat / 2 ∈
                      (ws1_b.take qb.toNat).map BitVec.toNat) ∧
                  (FullMem c { s with
                    core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                    scratch := { s.scratch with
                      work_stk1 := ws1_b, ant_sz := asz1, res_sz := 0#64 } } ⋆ R) mb)
              (fun _ ⟨qb, ⟨⟩⟩ mb
                  ⟨mrk_b, ws1_b, hqab, hqb_le, heq_ab, hqb, hcov_b, hmb⟩ => by
                have hcov_a' :
                    (s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
                    s.core.confl_lit0.toNat / 2 ∈
                      (ws1_b.take qb.toNat).map BitVec.toNat :=
                  hcov_a.elim Or.inl fun hm' => Or.inr (by
                    obtain ⟨k, hk, hkeq⟩ :=
                      (mem_map_take_iff (by have := hqa.2.1; omega)).mp hm'
                    exact (mem_map_take_iff (by have := hqb.2.1; omega)).mpr
                      ⟨k, by omega, by rw [heq_ab k hk, hkeq]⟩)
                exact hJq qb mrk_b ws1_b asz1 0#64 mb hqb_le hqb
                  (fun _ => by
                    simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct1]
                    exact ⟨hcov_a', hcov_b⟩) hsub1 hmb)
              (fun Jb hJb => by
                have hbv_lvl : (b_bv >>> 1#32).toNat < s.core.lvl.length := by omega
                have hbv_mrk : (b_bv >>> 1#32).toNat < mrk_a.length := by rw [hqa.1]; omega
                have hbv_idx : (b_bv >>> 1#32).toNat =
                    s.core.confl_lit1.toNat % 2 ^ 32 / 2 := by
                  rw [bv32_lshr1_toNat, hb_eq, Nat.mod_eq_of_lt hb32]
                have hbv_lvl' : s.core.confl_lit1.toNat % 2 ^ 32 / 2 <
                    s.core.lvl.length := by rw [← hbv_idx]; exact hbv_lvl
                have hbv_mrk' : s.core.confl_lit1.toNat % 2 ^ 32 / 2 <
                    mrk_a.length := by rw [← hbv_idx]; exact hbv_mrk
                have hqa_ws1 : qa.toNat < ws1_a.length := by have := hqa.2.1; omega
                fvt_steps
                · have hlp : 0 < (s.core.lvl[(b_bv >>> 1#32).toNat]?.getD 0#32).toNat := by
                    rw [List.getElem?_eq_getElem hbv_lvl, Option.getD_some]
                    have hlv : s.core.lvl[(b_bv >>> 1#32).toNat]'hbv_lvl =
                        s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_lvl' := by
                      congr 1
                    rw [hlv]; c0_bound
                  have hm0_b : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some]
                    have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                        mrk_a[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_mrk' := by
                      congr 1
                    rw [hmk]; exact (bv8_zext32_eq0_iff _).mp (by assumption)
                  have hqa1 : (qa + 1#64).toNat = qa.toNat + 1 := by bv_omega
                  obtain ⟨_, hqb_ok, hpre_b, _⟩ :=
                    push_queue_step hqa hcv_le hbv_cv hlp hm0_b hb_trl
                  have hb_mod :
                      (b_bv >>> 1#32).toNat % 2 ^ 64 = (b_bv >>> 1#32).toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have hm_b_ok := m6_fullMem_mrk_ws1_eq
                    (show mrk_a.set (s.core.confl_lit1.toNat % 2 ^ 32 / 2) 1#8 =
                      mrk_a.set (b_bv >>> 1#32).toNat 1#8 by rw [hbv_idx])
                    rfl hm
                  refine hJb (qa + 1#64, ()) _ ⟨_, _, by omega, by omega, hpre_b,
                    by simpa [hqa1, hb_mod] using hqb_ok, Or.inr ?_, hm_b_ok⟩
                  rw [hqa1]
                  exact (mem_map_take_iff (by simp [hqa.2.1]; omega)).mpr
                    ⟨qa.toNat, by omega, by
                      rw [List.getElem?_set_self hqa_ws1, Option.getD_some]
                      change (b_bv >>> 1#32).toNat = _
                      rw [bv32_lshr1_toNat, hb_eq]⟩
                · have hm0_b : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some]
                    have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                        mrk_a[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_mrk' := by
                      congr 1
                    rw [hmk]; exact (bv8_zext32_eq0_iff _).mp (by assumption)
                  have hlt := push_queue_lt hqa hcv_le hbv_cv hm0_b
                  have hle : s.core.cur_vars % 2 ^ 64 ≤ qa.toNat := by c0_bound
                  rw [Nat.mod_eq_of_lt (by omega)] at hle; omega
                · have hne0 : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk ≠ 0#8 := fun h => by
                    have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                        mrk_a[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_mrk' := by
                      congr 1
                    rw [hmk] at h
                    exact (by assumption :
                      (mrk_a[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_mrk').setWidth
                        32 ≠ 0#32) ((bv8_zext32_eq0_iff _).mpr h)
                  have hm1 : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 1#8 := by
                    rcases hqa.2.2.2.2.2.2.2.1 _ hbv_cv with h0 | h1
                    · rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some] at h0
                      exact absurd h0 hne0
                    · exact h1
                  exact hJb (qa, ()) ma ⟨mrk_a, ws1_a, Nat.le_refl _, hqa_le,
                    fun _ _ => rfl, hqa, Or.inr (by
                      have := (hqa.2.2.2.2.2.2.1 _ hbv_cv).mp hm1
                      rwa [bv32_lshr1_toNat, hb_eq] at this), hma⟩
                · have hlv0 :
                      (s.core.lvl[(b_bv >>> 1#32).toNat]?.getD 0#32).toNat = 0 := by
                    rw [List.getElem?_eq_getElem hbv_lvl, Option.getD_some]
                    have hlv : s.core.lvl[(b_bv >>> 1#32).toNat]'hbv_lvl =
                        s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'hbv_lvl' := by
                      congr 1
                    rw [hlv]; c0_bound
                  exact hJb (qa, ()) ma ⟨mrk_a, ws1_a, Nat.le_refl _, hqa_le,
                    fun _ _ => rfl, hqa,
                    Or.inl (by rwa [bv32_lshr1_toNat, hb_eq] at hlv0), hma⟩))
          (fun Ja hJa => by
            have hav_lvl : (a_bv >>> 1#32).toNat < s.core.lvl.length := by omega
            have hav_mrk : (a_bv >>> 1#32).toNat < s.core.mrk.length := by omega
            have hws1_0 : 0 < s.scratch.work_stk1.length := by omega
            have hav_idx : (a_bv >>> 1#32).toNat =
                s.core.confl_lit0.toNat % 2 ^ 32 / 2 := by
              rw [bv32_lshr1_toNat, ha_eq, Nat.mod_eq_of_lt ha32]
            have hav_lvl' : s.core.confl_lit0.toNat % 2 ^ 32 / 2 <
                s.core.lvl.length := by rw [← hav_idx]; exact hav_lvl
            have hav_mrk' : s.core.confl_lit0.toNat % 2 ^ 32 / 2 <
                s.core.mrk.length := by rw [← hav_idx]; exact hav_mrk
            fvt_steps
            · have hlp : 0 < (s.core.lvl[(a_bv >>> 1#32).toNat]?.getD 0#32).toNat := by
                rw [List.getElem?_eq_getElem hav_lvl, Option.getD_some]
                have hlv : s.core.lvl[(a_bv >>> 1#32).toNat]'hav_lvl =
                    s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'hav_lvl' := by
                  congr 1
                rw [hlv]; c0_bound
              have hm0_a : s.core.mrk[(a_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 :=
                hspW.2.2.1.1 _ (by omega)
              obtain ⟨_, hqa_ok, _, _⟩ :=
                push_queue_step hq0 hcv_le hav_cv hlp hm0_a ha_trl
              have ha_mod :
                  (a_bv >>> 1#32).toNat % 2 ^ 64 = (a_bv >>> 1#32).toNat :=
                Nat.mod_eq_of_lt (by omega)
              have hm_a_ok := m6_fullMem_mrk_ws1_eq
                (show s.core.mrk.set (s.core.confl_lit0.toNat % 2 ^ 32 / 2) 1#8 =
                  s.core.mrk.set (a_bv >>> 1#32).toNat 1#8 by rw [hav_idx])
                rfl hm
              refine hJa (1#64, ()) _ ⟨_, _, by show 1 ≤ _; omega,
                by simpa [ha_mod] using hqa_ok, Or.inr ?_, hm_a_ok⟩
              exact (mem_map_take_iff (by simp [hws1_len]; omega)).mpr
                ⟨0, by decide, by
                  rw [List.getElem?_set_self hws1_0, Option.getD_some]
                  change (a_bv >>> 1#32).toNat = _
                  rw [bv32_lshr1_toNat, ha_eq]⟩
            · exfalso
              have h0 : s.core.mrk[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'hav_mrk' = 0#8 := by
                have h := hspW.2.2.1.1 _
                  (by omega : s.core.confl_lit0.toNat % 2 ^ 32 / 2 < c.max_vars)
                rwa [List.getElem?_eq_getElem hav_mrk', Option.getD_some] at h
              exact hc ((bv8_zext32_eq0_iff _).mpr h0)
            · have hlv0 :
                  (s.core.lvl[(a_bv >>> 1#32).toNat]?.getD 0#32).toNat = 0 := by
                rw [List.getElem?_eq_getElem hav_lvl, Option.getD_some]
                have hlv : s.core.lvl[(a_bv >>> 1#32).toNat]'hav_lvl =
                    s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'hav_lvl' := by
                  congr 1
                rw [hlv]; c0_bound
              exact hJa (0#64, ()) m_sb ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _,
                hq0, Or.inl (by rwa [bv32_lshr1_toNat, ha_eq] at hlv0), hm_sb⟩))
      (fun Jsb hJsb => by
        fvt_steps; c0_call hSubBin
        refine ⟨c, _, R, rfl,
          m6_deduce_state_len hspW.1 hmrk_len hlm1_len hws1_len hws2_len,
          by rw [ha_eq]; exact ha_lt, by rw [hb_eq]; exact hb_lt, hm, fun ok => ?_⟩
        fvt_steps
        · exact hJsb () _ ⟨0xFFFFFFFFFFFFFFFE#64, Or.inr (Or.inl rfl), hm⟩
        · exact hJsb () _ ⟨0xFFFFFFFFFFFFFFFF#64, Or.inl rfl, hm⟩)
  · exact absurd (hct1.symm.trans hct2) (by decide)
  · exact absurd (hct1.symm.trans hct0) (by decide)

/-- `full_viv_deduce_m6` satisfies `fullVivDeduceM6Spec` parametrically in `Γ`. -/
theorem full_viv_deduce_m6_wp (Γ : Env)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivDeduceM6Spec a m Q X →
      Func.wp Γ full_viv_deduce_m6_body a m Q X := by
  rintro ⟨h, cref, sz, implied, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hspW, href, hng, hsz_le, htmp_lt, hconfl, himp, hm0, hQ⟩
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have halen_le := hcl.arena_len_le; have har_len := hcl.arena_len_arr
  have hmrk_len := hcl.mrk_len; have hlm_len := hcl.lit_mark_len
  have hlvl_len := hcl.lvl_len; have htrl_len := hcl.trl_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  have hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0 :=
    ⟨hmrk_len, hws1_len, Nat.zero_le _, fun _ h => (by cases h), by simp,
     fun _ h => (by cases h),
     fun v hv => ⟨fun h => (by rw [hspW.2.2.1.1 v (by omega)] at h; cases h),
       fun h => (by simp at h)⟩,
     fun v hv => Or.inl (hspW.2.2.1.1 v (by omega)), fun v _ hv => hspW.2.2.1.1 v hv⟩
  unfold Func.wp full_viv_deduce_m6_body
  fvt_to_group
  -- Loop 0: mark `lit_mark[tmp[mi]] = 1` for `mi < sz`
  refine wp_loop_inv (ts := [i32])
    (fun (mi, ()) m_lm =>
      mi.toNat ≤ sz.toNat ∧ ∃ lm1 : List (BitVec 8), lm1.length = 2 * c.max_vars ∧
        (∀ l < 2 * c.max_vars,
          lm1[l]?.getD 0#8 ≠ 0#8 → ∃ t < mi.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
        (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) m_lm)
    (fun (mi, _) _ => sz.toNat - mi.toNat) ?_ ?_
  · intro J0 hJ0; fvt_steps
    exact hJ0 (0#32, ()) m0 ⟨Nat.zero_le _, s.core.lit_mark, hlm_len,
      fun l hl hnz => absurd (hspW.2.2.1.2 l hl) hnz, hm0⟩
  · rintro J0 ⟨mi, ⟨⟩⟩ m_lm ⟨hmk_le, lm1, hlm1_len, hlm1_dom, hm_lm⟩ ih0
    fvt_step; fvt_step
    · have hmk_lt : mi.toNat < sz.toNat := by c0_bound
      have hmk1 : (mi + 1#32).toNat = mi.toNat + 1 := by bv_omega
      have hmk_tmp : mi.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
      let lt := s.core.tmp[mi.toNat]'hmk_tmp
      have hlt_lm : lt.toNat < lm1.length := by
        have := htmp_lt mi.toNat hmk_lt
        rw [List.getElem?_eq_getElem hmk_tmp, Option.getD_some] at this
        dsimp only [lt]; omega
      fvt_steps
      let lm1' := lm1.set lt.toNat 1#8
      refine ih0 (mi + 1#32, ()) _ (by dsimp only; omega)
        ⟨by omega, lm1', by simp [lm1', hlm1_len], fun q hq hnz => ?_, by assumption⟩
      by_cases hql : q = lt.toNat
      · subst hql; exact ⟨mi.toNat, by omega, by
          rw [List.getElem?_eq_getElem hmk_tmp, Option.getD_some]⟩
      · dsimp only [lm1'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
        obtain ⟨t, ht, hteq⟩ := hlm1_dom q hq hnz; exact ⟨t, by omega, hteq⟩
    · have hmk_eq : mi.toNat = sz.toNat := by c0_bound
      have hlm1_dom' : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
          ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l := fun l hl hnz => by
        obtain ⟨t, ht, he⟩ := hlm1_dom l hl hnz; exact ⟨t, by omega, he⟩
      clear hc ih0 J0
      fvt_to_group
      -- Phase 1 join -> call `m6_deduce_phase2_wp`
      refine wp_join_group (ts := [i64, i32])
        (fun (qlen_v, olen_v, ()) mp =>
          ∃ (mrk1 : List (BitVec 8)) (ws1_1 ws2_1 : List (BitVec 32)) (asz1 rsz1 : BitVec 64),
            ws2_1.length = 2 * c.max_vars ∧ qlen_v.toNat ≤ s.core.cur_vars ∧
            VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
            VivOutOk s implied ws1_1 ws2_1 0 olen_v.toNat false ∧
            VivSeedOk s cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false ∧
            M6SubRefOk s asz1 ∧
            (implied ≠ 0xFFFFFFFF#32 →
              (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk1, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_1, work_stk2 := ws2_1, ant_sz := asz1, res_sz := rsz1 } }
              ⋆ R) mp)
        (fun _ ⟨qlen_v, olen_v, ⟨⟩⟩ mp
            ⟨mrk1, ws1_1, ws2_1, asz1, rsz1, hws2_1, hql1, hq1, ho1, hsd1, hsub1, hsdi1, hmp⟩ =>
          m6_deduce_phase2_wp Γ hSubBin hSubCl hspW href hng hsz_le htmp_lt hconfl himp hlm1_len
            hlm1_dom' hws2_1 hql1 hq1 ho1 hsd1 hsub1 hsdi1 hmp hQ)
        (fun Jp hJp => ?_)
      fvt_to_group
      · -- Phase 1A: `implied ≠ 0xFFFFFFFFu`
        have himp_ne : implied ≠ 0xFFFFFFFF#32 := by c0_bound
        obtain ⟨himp_lt, himp_v1⟩ := himp himp_ne
        let iv_bv := implied >>> 1#32
        have hiv_val : iv_bv.toNat = implied.toNat / 2 := bv32_lshr1_toNat _
        have hiv_cv : iv_bv.toNat < s.core.cur_vars := by rw [hiv_val]; omega
        have hiv_lvl : iv_bv.toNat < s.core.lvl.length := by omega
        have hiv_mrk : iv_bv.toNat < s.core.mrk.length := by omega
        have hws1_0 : 0 < s.scratch.work_stk1.length := by omega
        have hws2_0 : 0 < s.scratch.work_stk2.length := by omega
        have hiv_trl : ∃ m < s.core.trail_end,
            (s.core.trl[m]?.getD 0#32).toNat / 2 = iv_bv.toNat := by
          obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_true_iff _ himp_lt).mp himp_v1
          exact ⟨m, hm_lt, by rw [hmeq, hiv_val]⟩
        refine wp_join_group (ts := [i64])
          (fun (qlen_v, ()) m1 => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32)),
            qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
            ((s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk1, lit_mark := lm1 }
              scratch := { s.scratch with
                work_stk1 := ws1_1, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m1)
          (fun _ ⟨qlen_v, ⟨⟩⟩ m1 ⟨mrk1, ws1_1, hql1, hq1, hcov_i, hm1⟩ => by
            fvt_steps
            let ws2_1 := s.scratch.work_stk2.set 0 implied
            have hws2_1 : ws2_1.length = 2 * c.max_vars := by simp [ws2_1, hws2_len]
            refine hJp (qlen_v, 1#32, ()) _ ⟨mrk1, ws1_1, ws2_1, 0xFFFFFFFFFFFFFFFF#64, 0#64,
              hws2_1, hql1, hq1, ?_, ?_, Or.inl rfl, fun _ => hcov_i, by assumption⟩
            · intro _
              refine ⟨by show 1 ≤ s.core.cur_vars; omega, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
              · have hj0 : j = 0 := by change j < 1 at hj; omega
                subst hj0; dsimp only [ws2_1]
                rw [List.getElem?_set_self hws2_0, Option.getD_some]; exact himp_lt
              · show ((ws2_1.take 1).map BitVec.toNat |>.map (· / 2)).Nodup
                rw [List.take_one]; cases ws2_1.head? <;> simp
              · intro j hj; have hj0 : j = 0 := by change j < 1 at hj; omega
                subst hj0; left; dsimp only [ws2_1]
                rw [List.getElem?_set_self hws2_0, Option.getD_some]; exact ⟨himp_ne, rfl, rfl⟩
              · intro _
                exact ⟨by decide, by dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0]⟩
              · intro _ h; exact absurd h (Nat.not_lt_zero _)
            · intro _; simp only [himp_ne, ne_eq, not_false_eq_true, ↓reduceIte]
              exact (mem_map_take_iff (by show 1 ≤ ws2_1.length; rw [hws2_1]; omega)).mpr
                ⟨0, by decide, by dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0]; rfl⟩)
          (fun J1 hJ1 => by
            fvt_steps
            · have hlvl_pos : 0 < (s.core.lvl[iv_bv.toNat]?.getD 0#32).toNat := by
                rw [List.getElem?_eq_getElem hiv_lvl, Option.getD_some]; c0_bound
              have hm0' : s.core.mrk[iv_bv.toNat]?.getD 0#8 = 0#8 :=
                hspW.2.2.1.1 iv_bv.toNat (by omega)
              obtain ⟨_, hq_next, _, _⟩ := push_queue_step hq0 hcv_le hiv_cv hlvl_pos hm0' hiv_trl
              have hiv_mod : iv_bv.toNat % 2 ^ 64 = iv_bv.toNat := Nat.mod_eq_of_lt (by omega)
              refine hJ1 (1#64, ()) _ ⟨_, _, by show 1 ≤ _; omega, by simpa [hiv_mod] using hq_next,
                Or.inr ((mem_map_take_iff (by simp [hws1_len]; omega)).mpr
                  ⟨0, by decide, by
                    rw [List.getElem?_set_self hws1_0, Option.getD_some]; exact hiv_val⟩),
                by assumption⟩
            · have hlvl0 : (s.core.lvl[iv_bv.toNat]?.getD 0#32).toNat = 0 := by
                rw [List.getElem?_eq_getElem hiv_lvl, Option.getD_some]
                have hlv : s.core.lvl[iv_bv.toNat]'hiv_lvl =
                    s.core.lvl[implied.toNat / 2]'(by rw [← hiv_val]; exact hiv_lvl) := by
                  congr 1
                rw [hlv]; c0_bound
              exact hJ1 (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _, hq0,
                Or.inl (by rwa [← hiv_val]), hm⟩)
      · -- Phase 1B: `implied == 0xFFFFFFFFu`
        have himp_eq : implied = 0xFFFFFFFF#32 := by c0_bound
        refine wp_join_group (ts := [i32])
          (fun (src_cr, ()) m_src => m = m_src ∧
            src_cr.toNat =
              (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∧
            src_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s src_cr.toNat = false)
          (fun _ ⟨src_cr, ⟨⟩⟩ m_src ⟨hm_src, hsrc_eq, hsrc_ref, hsrc_ng⟩ => by
            subst hm_src
            refine wp_join_group (ts := [i64])
              (fun (qlen_v, ()) m_q => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
                  (asz1 rsz1 : BitVec 64),
                qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
                VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false ∧
                M6SubRefOk s asz1 ∧
                (FullMem c { s with
                  core := { s.core with mrk := mrk1, lit_mark := lm1 }
                  scratch := { s.scratch with
                    work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) m_q)
              (fun _ ⟨qlen_v, ⟨⟩⟩ m_q ⟨mrk1, ws1_1, asz1, rsz1, hql1, hq1, hsd1, hsub1, hm_q⟩ =>
                hJp (qlen_v, 0#32, ()) m_q ⟨mrk1, ws1_1, s.scratch.work_stk2, asz1, rsz1,
                  hws2_len, hql1, hq1,
                  fun _ => ⟨Nat.zero_le _, fun _ h => by simp at h, by simp,
                    fun _ h => by simp at h,
                    fun hne => absurd himp_eq hne, fun _ h => by omega⟩,
                  hsd1, hsub1, fun hne => absurd himp_eq hne, hm_q⟩)
              (fun Jq hJq => ?_)
            fvt_step; fvt_step; rw [wp_jnz]; constructor <;> intro hc
            · -- `confl_type == 1`: binary conflict `(a, b)`
              have hct1 : s.core.confl_type = 1#64 := by
                simp only [Arg.val_var, beq_iff_eq] at hc; exact hc
              exact m6_deduce_phase1b_bin_wp Γ hSubBin hspW hlm1_len himp_eq hct1 hconfl hq0 hm
                fun qlen_v mrk1 ws1_1 asz1 rsz1 m_q h1 h2 h3 h4 h5 =>
                  hJq (qlen_v, ()) m_q ⟨mrk1, ws1_1, asz1, rsz1, h1, h2, h3, h4, h5⟩
            · -- `confl_type ≠ 1`: seed from `src_cr`
              have hct_ne1 : s.core.confl_type ≠ 1#64 := by
                simp only [Arg.val_var, beq_eq_false_iff_ne] at hc; exact hc
              have hsrc_wf := hw.arena.refs_wf src_cr.toNat hsrc_ref
              have hsrc_bd : src_cr.toNat + 3 + fullArenaClauseSizeCore s.core src_cr.toNat ≤
                  s.core.arena.length := by omega
              have hfal_src : ∀ l ∈ fullArenaClauseLits s src_cr.toNat,
                  s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
                rcases hconfl himp_eq with (⟨hct1, _⟩ | ⟨hct2, _, _, hfal2⟩) | ⟨hct0, hfal0⟩
                · exact absurd hct1 hct_ne1
                · have : src_cr.toNat = s.core.confl_ref.toNat := by simpa [hct2] using hsrc_eq
                  rwa [this]
                · have hne2 : s.core.confl_type ≠ 2#64 := by rw [hct0]; decide
                  have : src_cr.toNat = cref.toNat := by simpa [hne2] using hsrc_eq
                  rwa [this]
              refine wp_join_group (ts := [i64]) Jq
                (fun _ ⟨q, ⟨⟩⟩ mq h => by fvt_steps; exact h) (fun _ hJw => by
                fvt_to_group
                have hsrc2 :
                    (src_cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
                have hsrc_ar : src_cr.toNat < s.core.arena.length := by omega
                let csz_bv := s.core.arena[(src_cr.setWidth 64 + 2#64).toNat]'hsrc2
                have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core src_cr.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  dsimp only [csz_bv]; simp only [show (src_cr.setWidth 64 + 2#64).toNat =
                    src_cr.toNat + 2 by bv_omega]
                refine wp_join_group (ts := [])
                  (fun _ m_rs => ∃ (asz1 rsz1 : BitVec 64), M6SubRefOk s asz1 ∧
                    (FullMem c { s with
                      core := { s.core with lit_mark := lm1 }
                      scratch := { s.scratch with ant_sz := asz1, res_sz := rsz1 } } ⋆ R) m_rs)
                  (fun _ _ m_rs ⟨asz1, rsz1, hsub1, hm_rs⟩ => by
                    fvt_to_group
                    refine wp_loop_inv (ts := [i64, i32])
                      (fun (qlen_i, i_c, ()) mi =>
                        ∃ (mrk_i : List (BitVec 8)) (ws1_i : List (BitVec 32)),
                          i_c.toNat ≤ csz_bv.toNat ∧ qlen_i.toNat ≤ s.core.cur_vars ∧
                          VivQueueOk c s mrk_i ws1_i qlen_i.toNat ∧
                          (∀ t < i_c.toNat,
                            (s.core.lvl[(s.core.arena[src_cr.toNat + 3 + t]?.getD 0#32).toNat /
                              2]?.getD 0#32).toNat = 0 ∨
                            (s.core.arena[src_cr.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
                              (ws1_i.take qlen_i.toNat).map BitVec.toNat) ∧
                          (FullMem c { s with
                            core := { s.core with mrk := mrk_i, lit_mark := lm1 }
                            scratch := { s.scratch with
                              work_stk1 := ws1_i, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) mi)
                      (fun (_, i_c, ()) _ => csz_bv.toNat - i_c.toNat) ?_ ?_
                    · intro Ji hJi; fvt_steps
                      exact hJi (0#64, 0#32, ()) m_rs ⟨s.core.mrk, s.scratch.work_stk1, by simp,
                        Nat.zero_le _, hq0, fun _ ht => by simp at ht, hm_rs⟩
                    · rintro Ji ⟨qlen_i, i_c, ⟨⟩⟩ mi
                        ⟨mrk_i, ws1_i, hi_le, hql_i, hqi_ok, hcov_i, hmi⟩ ihi
                      fvt_step; fvt_step
                      · have hi_lt : i_c.toNat < csz_bv.toNat := by dsimp only [csz_bv]; c0_bound
                        have hi1 : (i_c + 1#32).toNat = i_c.toNat + 1 := by bv_omega
                        have hli_idx : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat =
                            src_cr.toNat + 3 + i_c.toNat := by bv_omega
                        have hli_ar : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat <
                            s.core.arena.length := by omega
                        let l_bv :=
                          s.core.arena[(src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat]'hli_ar
                        let lv_bv := l_bv >>> 1#32
                        have hl_eq :
                            l_bv = s.core.arena[src_cr.toNat + 3 + i_c.toNat]'(by omega) := by
                          dsimp only [l_bv]; simp only [hli_idx]
                        have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s src_cr.toNat :=
                          (mem_fullArenaClauseLitsCore_iff hsrc_bd).mpr
                            ⟨i_c.toNat, by rw [← hcsz_eq]; exact hi_lt,
                             congrArg BitVec.toNat hl_eq.symm⟩
                        have hl_lt : l_bv.toNat < 2 * s.core.cur_vars :=
                          hw.arena.lits_lt src_cr.toNat hsrc_ref hsrc_ng l_bv.toNat hl_mem
                        have hlv_val : lv_bv.toNat = l_bv.toNat / 2 := bv32_lshr1_toNat _
                        have hlv_cv : lv_bv.toNat < s.core.cur_vars := by rw [hlv_val]; omega
                        have hlv_trl : ∃ m < s.core.trail_end,
                            (s.core.trl[m]?.getD 0#32).toNat / 2 = lv_bv.toNat := by
                          obtain ⟨m, hm_lt, hmeq⟩ :=
                            (hw.vals_false_iff l_bv.toNat hl_lt).mp (hfal_src l_bv.toNat hl_mem)
                          exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, hlv_val]⟩
                        fvt_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (qlen_i', ()) mo =>
                            ∃ (mrk_o : List (BitVec 8)) (ws1_o : List (BitVec 32)),
                              qlen_i.toNat ≤ qlen_i'.toNat ∧ qlen_i'.toNat ≤ s.core.cur_vars ∧
                              (∀ k < qlen_i.toNat, ws1_o[k]? = ws1_i[k]?) ∧
                              VivQueueOk c s mrk_o ws1_o qlen_i'.toNat ∧
                              ((s.core.lvl[lv_bv.toNat]?.getD 0#32).toNat = 0 ∨
                                lv_bv.toNat ∈ (ws1_o.take qlen_i'.toNat).map BitVec.toNat) ∧
                              (FullMem c { s with
                                core := { s.core with mrk := mrk_o, lit_mark := lm1 }
                                scratch := { s.scratch with
                                  work_stk1 := ws1_o, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) mo)
                          (fun _ ⟨qlen_i', ⟨⟩⟩ mo
                              ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩ => by
                            fvt_steps
                            have hws1_o_len : ws1_o.length = 2 * c.max_vars := hqo.2.1
                            refine ihi (qlen_i', i_c + 1#32, ()) mo (by dsimp only; omega)
                              ⟨mrk_o, ws1_o, by omega, hql_o, hqo, fun t ht => ?_, hmo⟩
                            rcases (by omega : t < i_c.toNat ∨ t = i_c.toNat) with ht' | rfl
                            · refine (hcov_i t ht').elim Or.inl fun hm' => Or.inr ?_
                              obtain ⟨k, hk, hkeq⟩ :=
                                (mem_map_take_iff (by have := hqi_ok.2.1; omega)).mp hm'
                              exact (mem_map_take_iff (by omega)).mpr
                                ⟨k, by omega, by rw [heq_o k hk, hkeq]⟩
                            · have hleq :
                                  (s.core.arena[src_cr.toNat + 3 + i_c.toNat]?.getD 0#32).toNat /
                                    2 = lv_bv.toNat := by
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                                  ← hl_eq, hlv_val]
                              rw [hleq]; exact hcov_lv)
                          (fun Jo hJo => m6_push_branch_step hspW.1 hqi_ok hlv_cv hlv_trl hmi
                            fun qlen' mrk_o ws1_o mo hq_io hql_o heq_o hqo hcov_lv hmo =>
                              hJo (qlen', ()) mo
                                ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩)
                      · have hge_csz : csz_bv.toNat ≤ i_c.toNat := by dsimp only [csz_bv]; c0_bound
                        have hi_eq : i_c.toNat = csz_bv.toNat := by omega
                        have hcov_src : ∀ l ∈ fullArenaClauseLits s src_cr.toNat,
                            (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
                            l / 2 ∈ (ws1_i.take qlen_i.toNat).map BitVec.toNat := fun l hl => by
                          obtain ⟨t, ht, hlt⟩ := (mem_fullArenaClauseLitsCore_iff hsrc_bd).mp hl
                          have ht_bd : src_cr.toNat + 3 + t < s.core.arena.length := by omega
                          rw [← hcsz_eq] at ht; have hc' := hcov_i t (by omega)
                          rwa [List.getElem?_eq_getElem ht_bd, Option.getD_some, hlt] at hc'
                        exact hJw (qlen_i, ()) mi (hJq (qlen_i, ()) mi
                          ⟨mrk_i, ws1_i, asz1, rsz1, hql_i, hqi_ok,
                            fun _ => by
                              simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct_ne1]
                              have hsrc_c : (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat
                                else cref.toNat) = src_cr.toNat := hsrc_eq.symm
                              rwa [hsrc_c], hsub1, hmi⟩))
                  (fun Jrs hJrs => by
                    fvt_to_group
                    · refine wp_join_group (ts := [])
                        (fun _ m_r => ∃ rsz_r : BitVec 64,
                          (FullMem c { s with
                            core := { s.core with lit_mark := lm1 }
                            scratch := { s.scratch with
                              ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_r } } ⋆ R) m_r)
                        (fun _ _ m_r ⟨rsz_r, hm_r⟩ => by
                          fvt_steps; c0_call hSubCl
                          refine ⟨c, F0, F_cur, _, R, rfl,
                            m6_deduce_state_len hspW.1 hmrk_len hlm1_len hws1_len hws2_len,
                            m6_deduce_state_witness hw, hsrc_ref, hsrc_ng, hm_r, fun ok => ?_⟩
                          fvt_steps
                          · exact hJrs () _
                              ⟨src_cr.setWidth 64, rsz_r, m6_subRef_set_ref hsrc_ref, hm⟩
                          · exact hJrs () m_r ⟨0xFFFFFFFFFFFFFFFF#64, rsz_r, Or.inl rfl, hm_r⟩)
                        (fun Jr1 hJr1 => by
                          fvt_steps
                          · exact hJr1 () _ ⟨1#64, hm⟩
                          · exact hJr1 () _ ⟨0#64, hm⟩)
                    · exact hJrs () _ ⟨0xFFFFFFFFFFFFFFFF#64, 0#64, Or.inl rfl, hm⟩)))
          (fun Jsrc hJsrc => by
            fvt_steps
            · have hct2 : s.core.confl_type = 2#64 := by c0_bound
              rcases hconfl himp_eq with (⟨hct1, _⟩ | ⟨_, href2, hng2, _⟩) | ⟨hct0, _⟩
              · exact absurd (hct2.symm.trans hct1) (by decide)
              · have hlt32 : s.core.confl_ref.toNat < 2 ^ 32 := by
                  have := (hw.arena.refs_wf _ href2).1; omega
                have htr : (s.core.confl_ref.truncate 32).toNat = s.core.confl_ref.toNat :=
                  bv64_trunc32_toNat hlt32
                exact hJsrc (s.core.confl_ref.truncate 32, ()) _
                  ⟨rfl, by simp [hct2, htr], by rwa [htr], by rwa [htr]⟩
              · exact absurd (hct2.symm.trans hct0) (by decide)
            · have hne2 : s.core.confl_type ≠ 2#64 := by c0_bound
              exact hJsrc (cref, ()) _ ⟨rfl, by simp [hne2], href, hng⟩)

end DeduceProof

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
