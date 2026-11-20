module

public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas1
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Tiered Clause Vivification Proofs — Hub (`full_viv_deduce` & exports)

Re-exports Parts 1–2 (`full_viv_sort_lits_wp`, `full_viv_simplify_wp`, `full_viv_commit_wp`)
and proves `full_viv_deduce_wp` for `full_viv_deduce` (`Stage 4`, UNSAT-only).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. `full_viv_deduce` specification (`FullVivifySpecs`) -/

namespace FullVivifySpecs

/-- Specification for `full_viv_deduce(h, cref, implied, out)`: backward unit/reason analysis
from a probe propagation or conflict, clearing `mrk` on exit and proving `F_cur ⊨ out[0..<olen]`
whenever `olen < fullArenaClauseSize s cref.toNat`. -/
def fullVivDeduceSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, cref, implied, out_ptr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧
      FullSparseInv c F0 s ∧ FullWitnessInv c F0 F_cur s.core ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      (implied = 0xFFFFFFFF#32 →
        FullVivConflictOk F_cur s ∨
        (s.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
      (implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ olen mrk' ws1' ws2' rsz' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk' }
            scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
        FullSparseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core →
        olen.toNat ≤ c.max_vars →
        (olen.toNat < fullArenaClauseSize s cref.toNat →
          (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (olen, ()) m'

end FullVivifySpecs

section

open FullVivifyTactics FullVivifySpecs FullVivifyHelpers
open scoped FullArenaTactics FullVivifyTactics

/-! ## 2. Local tactics, zero-offset stack accessors, and pure BFS helpers -/

local macro "fv_while" : tactic =>
  `(tactic| ((try fv_unmdata); (repeat fv_strip); c0_step; c0_step))
local macro "fv_to_grp" : tactic => `(tactic| ((try fv_unmdata); (repeat fv_strip); fv_to_group))

@[local c0_load] private theorem c0_load_ws1_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + 0#64) = some s.scratch.work_stk1[0] :=
  FullArenaTactics.load_full_work_stk1 hi hm
@[local c0_load] private theorem c0_load_ws1_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using FullArenaTactics.load_full_work_stk1 hi hm
@[local c0_store] private theorem c0_store_ws1_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk1 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm
@[local c0_store] private theorem c0_store_ws1_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWorkStk1 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm
@[local c0_store] private theorem c0_store_ws2_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 (c.pWorkStk2 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm
@[local c0_store] private theorem c0_store_ws2_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWorkStk2 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

/-! ## 3. Factored sub-expression `wp` lemmas (`deduce_*`) -/

private abbrev deduceLargeRsnExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (rsn_bv v_bv : Val i32) (qlen : Val i64) (J : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_10 =>
  fvOp32 (OpCode.cmp CmpOp.ule i64 Ty.bool (by decide))
    (Arg.var p3.fst, Arg.var ld_10, ()) fun pb =>
  Expr.jnz (Arg.var pb.fst)
    (Expr.group (sig := [[]]) (fun Js_r => Blocks.cons (fun (_ : Tup Val []) =>
      fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
      fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld_11 =>
      Expr.group (sig := [[i64, i32]]) (fun Js_2 => Blocks.cons (fun p_31 =>
        fvOp32 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_31.snd.fst, Arg.var ld_11, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
           fvOp32 (OpCode.zext 32 64) (Arg.var ld_11, ()) fun pz =>
           fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
           Expr.load i64 (Arg.var p48.fst) fun ld_12 =>
           fvOp32 (OpCode.cmp CmpOp.ule i64 Ty.bool (by decide))
             (Arg.var p.fst, Arg.var ld_12, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
              fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
              fvOp32 (OpCode.zext 32 64) (Arg.var p_31.snd.fst, ()) fun pz =>
              fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
              fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
              fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
              fvOp32 (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_ov =>
              Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                fvOp32 (OpCode.add i32) (Arg.var p_31.snd.fst, Arg.imm 1, ()) fun pj =>
                Expr.jump Js_2.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil)
                fun Js_n =>
              fvOp32 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                (Arg.var p_ov.fst, Arg.var v_bv, ()) fun p =>
              Expr.jnz (Arg.var p.fst)
                (deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_31.fst Js_n.fst)
                (Expr.jump Js_n.fst (Arg.var p_31.fst, ())))
             (Expr.jump J (Arg.var p_31.fst, ())))
          (Expr.jump J (Arg.var p_31.fst, ()))) Blocks.nil)
        fun Js_init => Expr.jump Js_init.fst (Arg.var qlen, Arg.imm 0, ())) Blocks.nil)
      fun Js_rs =>
      fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
      fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      fvOp32 (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
      fvOp32 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
         Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.jump Js_rs.fst ()))
        (Expr.jump Js_rs.fst ()))
    (Expr.jump J (Arg.var qlen, ()))

private theorem deduce_large_rsn_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {rsz_b : BitVec 64}
    {qlen_c : Val i64} {rsn_bv v_bv : Val i32} {idx0 : Nat} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} {J : Cont [i64]}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat) (hws2 : ws2_b.length = 2 * c.max_vars)
    (href_r : rsn_bv.toNat ∈ fullArenaClauseRefs s)
    (hng_r : fullArenaClauseGarb s rsn_bv.toNat = false)
    (hidx0 : idx0 < s.core.trail_end) (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hlits_r : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, res_sz := rsz_b } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32))
        (rsz_n : BitVec 64) mlg,
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, res_sz := rsz_n } } ⋆ R) mlg →
      J (qlen', ()) mlg) :
    wp Γ Q X (deduceLargeRsnExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 rsn_bv v_bv qlen_c J) m := by
  have hcl := hsp.1.lengths.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have htrl_len := hcl.trl_len; have hlvl_len := hcl.lvl_len
  have hwf_r := hw.arena.refs_wf rsn_bv.toNat href_r
  have hbd_r : rsn_bv.toNat + 3 + fullArenaClauseSizeCore s.core rsn_bv.toNat ≤
      s.core.arena.length := by omega
  have hql_le := hqb.2.2.1
  dsimp only [deduceLargeRsnExpr, fvOp32]
  fv_to_grp
  · have hrsn_ar : rsn_bv.toNat < s.core.arena.length := by omega
    have hrsn_2 : (rsn_bv.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
    have hrsn_2_mod : (rsn_bv.toNat + 2) % 2 ^ 64 = rsn_bv.toNat + 2 :=
      Nat.mod_eq_of_lt (by have := hwf_r.1; omega)
    have hrsn_2_eq : (rsn_bv.setWidth 64 + 2#64).toNat = rsn_bv.toNat + 2 := by bv_omega
    let rsz_bv := s.core.arena[(rsn_bv.setWidth 64 + 2#64).toNat]'hrsn_2
    have hrsz_raw : s.core.arena[rsn_bv.toNat + 2]'(by omega) = rsz_bv := by
      dsimp only [rsz_bv]; simp only [hrsn_2_eq]
    have hrsz_eq : rsz_bv.toNat = fullArenaClauseSizeCore s.core rsn_bv.toNat := by
      unfold fullArenaClauseSizeCore
      simp only [rsz_bv, hrsn_2_eq,
        List.getElem?_eq_getElem (by omega : rsn_bv.toNat + 2 < s.core.arena.length),
        Option.getD_some]
    fv_to_grp
    refine wp_join_group
      (fun (_ : Tup Val []) mrs => ∃ rsz_n : BitVec 64,
        (FullMem c { s with
          core := { s.core with mrk := mrk_b }
          scratch := { s.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, res_sz := rsz_n } } ⋆ R) mrs)
      (fun _ _ mrs ⟨rsz_n, hmrs⟩ => by
        fv_to_grp
        refine wp_loop_inv (ts := [i64, i32])
          (fun (qlen_j, j_c, ()) mj =>
            ∃ (mrk_j : List (BitVec 8)) (ws1_j : List (BitVec 32)),
              j_c.toNat ≤ rsz_bv.toNat ∧ qlen_c.toNat ≤ qlen_j.toNat ∧
              qlen_j.toNat ≤ s.core.cur_vars ∧
              (∀ k < qlen_c.toNat, ws1_j[k]? = ws1_b[k]?) ∧
              VivQueueOk c s mrk_j ws1_j qlen_j.toNat ∧
              (∀ t < j_c.toNat,
                let q := (s.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat
                q / 2 ≠ v_bv.toNat →
                  (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                  q / 2 ∈ (ws1_j.take qlen_j.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_j }
                scratch := { s.scratch with
                  work_stk1 := ws1_j, work_stk2 := ws2_b, res_sz := rsz_n } } ⋆ R) mj)
          (fun (_, j_c, ()) _ => rsz_bv.toNat - j_c.toNat)
          (fun Jj hJj => by
            fv_steps
            exact hJj (qlen_c, 0#32, ()) mrs
              ⟨mrk_b, ws1_b, by simp, Nat.le_refl _, hql_le, fun _ _ => rfl, hqb,
               fun _ ht => by simp at ht, hmrs⟩)
          (fun Jj (qlen_j, j_c, ()) mj
              ⟨mrk_j, ws1_j, hj_le, hq_le_j, hql_j, heq_j, hqj, hcov_j, hmj⟩ ihj => ?_)
        fv_while
        · have hj_lt : j_c.toNat < rsz_bv.toNat := by c0_bound
          have hj_bd : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat =
              rsn_bv.toNat + 3 + j_c.toNat := by bv_omega
          have hj_ar : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat <
              s.core.arena.length := by rw [hj_bd]; omega
          let qlit := s.core.arena[(rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat]'hj_ar
          have hqlit_eq :
              qlit = s.core.arena[rsn_bv.toNat + 3 + j_c.toNat]'(by omega) := by
            dsimp only [qlit]; simp only [hj_bd]
          have hqlit_mem : qlit.toNat ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat :=
            (mem_fullArenaClauseLitsCore_iff hbd_r).mpr
              ⟨j_c.toNat, by rw [← hrsz_eq]; exact hj_lt, congrArg BitVec.toNat hqlit_eq.symm⟩
          have hqlit_lt : qlit.toNat < 2 * s.core.cur_vars :=
            hw.arena.lits_lt _ href_r hng_r _ hqlit_mem
          let ov_bv := qlit >>> 1#32
          have hov_val : ov_bv.toNat = qlit.toNat / 2 := bv32_lshr1_toNat _
          have hov_cv : ov_bv.toNat < s.core.cur_vars := by rw [hov_val]; omega
          have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by bv_omega
          fv_to_grp
          · refine wp_join_group (ts := [i64])
              (fun (qlen_j', ()) ml =>
                ∃ (mrk_l : List (BitVec 8)) (ws1_l : List (BitVec 32)),
                  qlen_j.toNat ≤ qlen_j'.toNat ∧ qlen_j'.toNat ≤ s.core.cur_vars ∧
                  (∀ k < qlen_j.toNat, ws1_l[k]? = ws1_j[k]?) ∧
                  VivQueueOk c s mrk_l ws1_l qlen_j'.toNat ∧
                  (ov_bv.toNat ≠ v_bv.toNat →
                    (s.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
                    ov_bv.toNat ∈ (ws1_l.take qlen_j'.toNat).map BitVec.toNat) ∧
                  (FullMem c { s with
                    core := { s.core with mrk := mrk_l }
                    scratch := { s.scratch with
                      work_stk1 := ws1_l, work_stk2 := ws2_b, res_sz := rsz_n } } ⋆ R) ml)
              (fun _ (qlen_j', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok, hcov_ov, hml⟩ =>
                by
                fv_steps
                have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
                refine ihj (qlen_j', j_c + 1#32, ()) ml (by dsimp only; omega)
                  ⟨mrk_l, ws1_l, by omega, by omega, hql_l,
                   fun k hk => (heq_l k (by omega)).trans (heq_j k hk), hql_ok,
                   fun t ht hne => ?_, hml⟩
                rcases (by omega : t < j_c.toNat ∨ t = j_c.toNat) with ht' | rfl
                · refine (hcov_j t ht' hne).elim Or.inl fun hm' => Or.inr ?_
                  obtain ⟨k, hk, hkeq⟩ :=
                    (mem_map_take_iff (by have := hqj.2.1; omega)).mp hm'
                  exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq_l k hk, hkeq]⟩
                · have hqeq :
                      (s.core.arena[rsn_bv.toNat + 3 + j_c.toNat]?.getD 0#32).toNat / 2 =
                        ov_bv.toNat := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                      ← hqlit_eq, hov_val]
                  rw [hqeq] at hne ⊢; exact hcov_ov hne)
              (fun Jl hJl => by
                (try fv_unmdata); (repeat fv_strip); c0_step
                rw [LeanQbe.T.wp_jnz]
                refine ⟨fun hc => ?_, fun hc => ?_⟩
                · simp only [LeanQbe.T.Arg.val_var, bne_iff_ne, ne_eq] at hc
                  have hov_ne : ov_bv.toNat ≠ v_bv.toNat :=
                    fun h => hc (BitVec.eq_of_toNat_eq h)
                  have hov_trl : ∃ m < s.core.trail_end,
                      (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat := by
                    rcases hlits_r _ hqlit_mem with hsame | ⟨m, hm', hmeq, _⟩
                    · exfalso; apply hov_ne; rw [hov_val, hsame, htrl0]
                    · exact ⟨m, by omega, by rw [hmeq, fullInv_var_xor1, hov_val]⟩
                  exact deduce_push_wp Γ hsp hw hqj hws2 hov_cv hov_trl hmj
                    fun qlen' mrk_l ws1_l ml hq_jl hql_l heq_l hql_ok hcov_ov hml =>
                      hJl (qlen', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok,
                        fun _ => hcov_ov, hml⟩
                · simp only [LeanQbe.T.Arg.val_var, bne_eq_false_iff_eq] at hc
                  fv_steps
                  exact hJl (qlen_j, ()) mj ⟨mrk_j, ws1_j, Nat.le_refl _, hql_j,
                    fun _ _ => rfl, hqj,
                    fun hne => absurd (congrArg BitVec.toNat hc) hne, hmj⟩)
          · have hlt : s.core.arena_len % 2 ^ 64 <
                (rsn_bv.toNat + 3 + rsz_bv.toNat) % 2 ^ 64 := by
              simp at hc; try rw [hrsn_2_mod] at hc; try rw [hrsz_raw] at hc
              c0_bound
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
            have : rsn_bv.toNat + 3 + rsz_bv.toNat ≤ s.core.arena_len := by omega
            omega
        · have hrsn_2_mod' : (rsn_bv.toNat + 2) % 18446744073709551616 = rsn_bv.toNat + 2 :=
            Nat.mod_eq_of_lt (by have := hwf_r.1; omega)
          have hj_eq : j_c.toNat = rsz_bv.toNat := by
            simp at hc
            simp only [hrsn_2_mod', hrsz_raw] at hc
            exact Nat.le_antisymm hj_le hc
          exact hJ qlen_j mrk_j ws1_j rsz_n mj hq_le_j hql_j heq_j hqj
            (fun q hq hne => by
              obtain ⟨t, ht, hqt⟩ := (mem_fullArenaClauseLitsCore_iff hbd_r).mp hq
              have ht_lt : rsn_bv.toNat + 3 + t < s.core.arena.length := by omega
              rw [← hrsz_eq] at ht
              have hq' := hcov_j t (by omega) (by
                rw [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt]; exact hne)
              rwa [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt] at hq')
            hmj)
      (fun Jrs hJrs => by
        fv_steps
        · exact hJrs () _ ⟨1#64, hm⟩
        · exact hJrs () m ⟨rsz_b, hm⟩)


private abbrev deducePhase2Expr (h pVars pMark pLevel pRsns pArena pWs1 pWs2 : Val i64)
    (cref implied : Val i32) (qlen : Val i64) (olen : Val i32) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 96, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld_6 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 360, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld_7 =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun Js => Blocks.cons (fun p_11 =>
    fvOp32 (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
      (Arg.var p_11.snd.fst, Arg.var p_11.fst, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.mul i64) (Arg.var p_11.snd.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld_8 =>
       fvOp32 (OpCode.add i64) (Arg.var p_11.snd.fst, Arg.imm 1, ()) fun p_15 =>
       fvOp32 (OpCode.zext 32 64) (Arg.var ld_8, ()) fun p =>
       fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pRsns, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld_9 =>
       Expr.group (sig := [[i64, i32, .bool]]) (fun _ => Blocks.cons (fun p =>
         Expr.jump Js.fst (Arg.var p.fst, Arg.var p_15.fst, Arg.var p.snd.fst,
           Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Js_r =>
       fvOp32 (OpCode.cmp CmpOp.eq i32 Ty.bool (by decide))
         (Arg.var ld_9, Arg.imm 4294967295, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (fvOp32 (OpCode.zext 32 64) (Arg.var ld_8, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var ld_7, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun ld =>
          fvOp32 (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var ld_6, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun ld =>
          Expr.group (sig := [[i32, .bool]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump Js_r.fst (Arg.var p_11.fst, Arg.var p.fst, Arg.var p.snd.fst, ()))
            Blocks.nil) fun Js_d =>
          fvOp32 (OpCode.cmp CmpOp.eq i32 Ty.bool (by decide))
            (Arg.var ld, Arg.var implied, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.jump Js_d.fst (Arg.var p_11.snd.snd.fst, Arg.imm (t := .bool) true, ()))
            (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p =>
              Expr.jump Js_d.fst (Arg.var p.fst, Arg.var p_11.snd.snd.snd.fst, ())) Blocks.nil)
              fun Js_o =>
             fvOp32 (OpCode.zext 32 64) (Arg.var p_11.snd.snd.fst, ()) fun p27 =>
             fvOp32 (OpCode.sext 32 64) (Arg.imm (t := i32) 1, ()) fun p28 =>
             fvOp32 (OpCode.shl i64) (Arg.var pVars, Arg.var p28.fst, ()) fun p29 =>
             fvOp32 (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
               (Arg.var p27.fst, Arg.var p29.fst, ()) fun p30 =>
             Expr.jnz (Arg.var p30.fst)
               (fvOp32 (OpCode.zext 32 64) (Arg.var p_11.snd.snd.fst, ()) fun p31 =>
                fvOp32 (OpCode.mul i64) (Arg.var p31.fst, Arg.imm 4, ()) fun p32 =>
                fvOp32 (OpCode.add i64) (Arg.var pWs2, Arg.var p32.fst, ()) fun p =>
                fvOp32 (OpCode.xor i32) (Arg.var ld, Arg.imm 1, ()) fun p33 =>
                Expr.store (Arg.var p33.fst) (Arg.var p.fst)
                  (fvOp32 (OpCode.add i32) (Arg.var p_11.snd.snd.fst, Arg.imm 1, ()) fun p =>
                   Expr.jump Js_o.fst (Arg.var p.fst, ())))
               (Expr.jump Js_o.fst (Arg.var p_11.snd.snd.fst, ()))))
         (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump Js_r.fst (Arg.var p.fst, Arg.var p_11.snd.snd.fst,
              Arg.var p_11.snd.snd.snd.fst, ())) Blocks.nil) fun Js_g =>
          fvOp32 (OpCode.and i32) (Arg.var ld_9, Arg.imm 2147483648, ()) fun p =>
          fvOp32 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide)) (Arg.var p.fst, Arg.imm 0, ())
            fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.and i32) (Arg.var ld_9, Arg.imm 2147483647, ()) fun p =>
             fvOp32 (OpCode.lshr i32) (Arg.var p.fst, Arg.imm 1, ()) fun p_ov =>
             Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
               Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_b =>
             deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_11.fst Js_b.fst)
            (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
               Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_lg =>
             deduceLargeRsnExpr h pVars pMark pLevel pArena pWs1 ld_9 ld_8 p_11.fst Js_lg.fst)))
      (deduceClearExpr pArena pMark pWs1 p_11.fst cref p_11.snd.snd.fst p_11.snd.snd.snd.fst))
      Blocks.nil)
    fun Js => Expr.jump Js.fst
      (Arg.var qlen, Arg.imm 0, Arg.var olen, Arg.imm (t := .bool) false, ())

private theorem deduce_phase2_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk1 : List (BitVec 8)} {ws1_1 ws2_1 : List (BitVec 32)} {rsz1 : BitVec 64}
    {qlen_v : Val i64} {cref implied olen_v : Val i32} {mp : Mem 64}
    {Q : Post [i32]} {X : XPost}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hws2_1 : ws2_1.length = 2 * c.max_vars) (hql1 : qlen_v.toNat ≤ s.core.cur_vars)
    (hq1 : VivQueueOk c s mrk1 ws1_1 qlen_v.toNat)
    (ho1 : VivOutOk s implied ws1_1 ws2_1 0 olen_v.toNat false)
    (hsd1 : VivSeedOk s cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false)
    (hsd_imp1 : implied ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat)
    (hmp : (FullMem c { s with
      core := { s.core with mrk := mrk1 }
      scratch := { s.scratch with
        work_stk1 := ws1_1, work_stk2 := ws2_1, res_sz := rsz1 } } ⋆ R) mp)
    (hQ : ∀ olen mrk' ws1' ws2' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk' }
          scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
      FullSparseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core → olen.toNat ≤ c.max_vars →
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (olen, ()) m') :
    wp Γ Q X (deducePhase2Expr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pMark c.pLevel
      c.pReason c.pArena c.pWorkStk1 c.pWorkStk2 cref implied qlen_v olen_v) mp := by
  have hcl := hsp.1.lengths.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have hrsns_len := hcl.rsns_len; have htrl_len := hcl.trl_len; have htp_len := hcl.trail_pos_len
  dsimp only [deducePhase2Expr, fvOp32]
  fv_to_grp
  refine wp_loop_inv (ts := [i64, i64, i32, .bool])
    (fun (qlen_c, qi_c, olen_c, taut_c, ()) mb =>
      ∃ (mrk_b : List (BitVec 8)) (ws1_b ws2_b : List (BitVec 32)) (rsz_b : BitVec 64),
        ws2_b.length = 2 * c.max_vars ∧ qi_c.toNat ≤ qlen_c.toNat ∧
        qlen_c.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_b ws1_b qlen_c.toNat ∧
        VivClosedOk s implied ws1_b ws2_b qi_c.toNat qlen_c.toNat olen_c.toNat taut_c ∧
        VivOutOk s implied ws1_b ws2_b qi_c.toNat olen_c.toNat taut_c ∧
        VivSeedOk s cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat taut_c ∧
        (implied ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ (ws1_b.take qlen_c.toNat).map BitVec.toNat) ∧
        (FullMem c { s with
          core := { s.core with mrk := mrk_b }
          scratch := { s.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, res_sz := rsz_b } } ⋆ R) mb)
    (fun (_, qi_c, _, _, ()) _ => s.core.cur_vars - qi_c.toNat)
    (fun Jb hJb => by
      fv_steps
      exact hJb (qlen_v, 0#64, olen_v, false, ()) mp
        ⟨mrk1, ws1_1, ws2_1, rsz1, hws2_1, by simp, hql1, hq1,
         (fun _ h => absurd h (Nat.not_lt_zero _)), ho1, hsd1, hsd_imp1, hmp⟩)
    (fun Jb (qlen_c, qi_c, olen_c, taut_c, ()) mb
        ⟨mrk_b, ws1_b, ws2_b, rsz_b, hws2_b, hqi_le, hql_le, hqb, hcb, hob, hsdb, hsdi_b,
         hmb⟩ ihb => ?_)
  fv_while
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
    fv_to_grp
    refine wp_join_group (ts := [i64, i32, .bool])
      (fun (qlen', olen', taut', ()) mn =>
        ∃ (mrk_n : List (BitVec 8)) (ws1_n ws2_n : List (BitVec 32)) (rsz_n : BitVec 64),
          ws2_n.length = 2 * c.max_vars ∧ qi_c.toNat + 1 ≤ qlen'.toNat ∧
          qlen'.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_n ws1_n qlen'.toNat ∧
          VivClosedOk s implied ws1_n ws2_n (qi_c.toNat + 1) qlen'.toNat olen'.toNat taut' ∧
          VivOutOk s implied ws1_n ws2_n (qi_c.toNat + 1) olen'.toNat taut' ∧
          VivSeedOk s cref implied ws1_n ws2_n qlen'.toNat olen'.toNat taut' ∧
          (implied ≠ 0xFFFFFFFF#32 →
            (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
            implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
          (FullMem c { s with
            core := { s.core with mrk := mrk_n }
            scratch := { s.scratch with
              work_stk1 := ws1_n, work_stk2 := ws2_n, res_sz := rsz_n } } ⋆ R) mn)
      (fun Jn (qlen', olen', taut', ()) mn
          ⟨mrk_n, ws1_n, ws2_n, rsz_n, hws2_n, hqi1_le, hql_n, hqn, hcn, hon, hsdn,
           hsdi_n, hmn⟩ => by
        fv_steps
        exact ihb (qlen', qi_c + 1#64, olen', taut', ()) mn (by dsimp only; omega)
          ⟨mrk_n, ws1_n, ws2_n, rsz_n, hws2_n, by omega, hql_n, hqn, by simpa [hqi1] using hcn,
           by simpa [hqi1] using hon, hsdn, hsdi_n, hmn⟩)
      (fun Jn hJn => ?_)
    let rsn_bv := s.core.rsns[v_bv.toNat]'hv_rsn
    have hrsn_get : s.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
        rsn_bv := by
      dsimp only [rsn_bv]; rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some,
        List.getElem?_eq_getElem hv_rsn, Option.getD_some]
    have htrl0' : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
        (ws1_b[qi_c.toNat]?.getD 0#32).toNat := by
      rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
    fv_to_grp
    · have hrsn_eq : rsn_bv = 0xFFFFFFFF#32 := by c0_bound
      refine wp_join_group (ts := [i32, .bool])
        (fun (olen', taut', ()) md =>
          ∃ (ws2_d : List (BitVec 32)),
            ws2_d.length = 2 * c.max_vars ∧
            VivClosedOk s implied ws1_b ws2_d (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut' ∧
            VivOutOk s implied ws1_b ws2_d (qi_c.toNat + 1) olen'.toNat taut' ∧
            VivSeedOk s cref implied ws1_b ws2_d qlen_c.toNat olen'.toNat taut' ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_b }
              scratch := { s.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_d, res_sz := rsz_b } } ⋆ R) md)
        (fun _ (olen', taut', ()) md ⟨ws2_d, hws2_d, hcd, hod, hsdd, hmd⟩ => by
          fv_steps; exact hJn (qlen_c, olen', taut', ()) md
            ⟨mrk_b, ws1_b, ws2_d, rsz_b, hws2_d, by omega, hql_le, hqb, hcd, hod, hsdd,
             hsdi_b, hmd⟩)
        (fun Jd hJd => ?_)
      fv_to_grp
      · have htl_imp : (s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl) =
            implied := by c0_bound
        fv_steps
        exact hJd (olen_c, true, ()) mb
          ⟨ws2_b, hws2_b,
           (by by_cases ht : taut_c
               · subst ht; exact vivClosed_of_taut_true hcb (hrsn_get.trans hrsn_eq)
               · simp only [Bool.not_eq_true] at ht; subst ht
                 exact vivClosed_taut_true hcb hw.trail_vars_nodup hidx0 htrl0'
                   (by rwa [hrsn_get])),
           (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), hmb⟩
      · have htl_ne : (s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl) ≠
            implied := by c0_bound
        refine wp_join_group (ts := [i32])
          (fun (olen', ()) mo =>
            ∃ (ws2_o : List (BitVec 32)),
              ws2_o.length = 2 * c.max_vars ∧
              VivClosedOk s implied ws1_b ws2_o (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut_c ∧
              VivOutOk s implied ws1_b ws2_o (qi_c.toNat + 1) olen'.toNat taut_c ∧
              VivSeedOk s cref implied ws1_b ws2_o qlen_c.toNat olen'.toNat taut_c ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_b }
                scratch := { s.scratch with
                  work_stk1 := ws1_b, work_stk2 := ws2_o, res_sz := rsz_b } } ⋆ R) mo)
          (fun _ (olen', ()) mo ⟨ws2_o, hws2_o, hco, hoo, hsdo, hmo⟩ => by
            fv_steps; exact hJd (olen', taut_c, ()) mo ⟨ws2_o, hws2_o, hco, hoo, hsdo, hmo⟩)
          (fun Jo hJo => ?_)
        fv_steps
        · have hol_lt2 : olen_c.toNat < 2 * s.core.cur_vars := by c0_bound
          have hol_ws2 : olen_c.toNat < ws2_b.length := by omega
          have hol1 : (olen_c + 1#32).toNat = olen_c.toNat + 1 := by bv_omega
          fv_steps
          have htl_eq : s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl =
              s.core.trl[idx0]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [htp_eq]
          have hne' : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx0]?.getD 0#32) ≠ implied :=
            fun _ => by rw [← htl_eq]; exact htl_ne
          by_cases ht : taut_c
          · subst ht
            exact hJo (olen_c + 1#32, ()) _
              ⟨_, (by rw [List.length_set]; exact hws2_b),
               vivClosed_of_taut_true hcb (hrsn_get.trans hrsn_eq),
               (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), hm⟩
          · simp only [Bool.not_eq_true] at ht; subst ht
            obtain ⟨_, _, hoo, hco, hpre2⟩ := vivOut_push_step hw hqb hqi_lt hob hcb himp hidx0
              htrl0' (by rwa [hrsn_get]) hne' hws2_b hcv_le
            have hws2_eq : ws2_b.set olen_c.toNat
                (s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl ^^^ 1#32) =
                ws2_b.set olen_c.toNat ((s.core.trl[idx0]?.getD 0#32) ^^^ 1#32) := by
              rw [htl_eq]
            have hmem2 : ∀ l, l ∈ (ws2_b.take olen_c.toNat).map BitVec.toNat →
                l ∈ ((ws2_b.set olen_c.toNat ((s.core.trl[idx0]?.getD 0#32) ^^^
                  1#32)).take (olen_c.toNat + 1)).map BitVec.toNat := fun l hl => by
              obtain ⟨i, hi, rfl⟩ := (mem_map_take_iff (by omega)).mp hl
              exact (mem_map_take_iff (by simp [hws2_b]; omega)).mpr
                ⟨i, by omega, by rw [hpre2 i hi]⟩
            refine hJo (olen_c + 1#32, ()) _
              ⟨ws2_b.set olen_c.toNat ((s.core.trl[idx0]?.getD 0#32) ^^^ 1#32),
               by rw [List.length_set]; exact hws2_b, ?_, ?_, ?_, ?_⟩
            · simpa [hol1] using hco
            · simpa [hol1] using hoo
            · intro _; rw [hol1]; have hs' := hsdb rfl
              by_cases himp_f : implied = 0xFFFFFFFF#32
              · simp only [himp_f, ne_eq, not_true_eq_false, ↓reduceIte] at hs' ⊢; exact hs'
              · simp only [himp_f, ne_eq, not_false_eq_true, ↓reduceIte] at hs' ⊢
                exact hmem2 _ hs'
            · rw [← hws2_eq]; exact hm
        · have hol_ge2 : 2 * s.core.cur_vars ≤ olen_c.toNat := by c0_bound
          have htl_eq : s.core.trl[(s.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl =
              s.core.trl[idx0]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [htp_eq]
          have hne' : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx0]?.getD 0#32) ≠ implied :=
            fun _ => by rw [← htl_eq]; exact htl_ne
          by_cases ht : taut_c
          · subst ht
            exact hJo (olen_c, ()) mb
              ⟨ws2_b, hws2_b, vivClosed_of_taut_true hcb (hrsn_get.trans hrsn_eq),
               (fun h => absurd h (by decide)), (fun h => absurd h (by decide)), hmb⟩
          · simp only [Bool.not_eq_true] at ht; subst ht
            have ⟨hol_lt, _⟩ := vivOut_push_lt hw hqb hcv_le hqi_lt hob himp hidx0 htrl0' hne'
              (by have := (hob rfl).1; omega)
            omega
    · have hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32 := by c0_bound
      refine wp_join_group (ts := [i64])
        (fun (qlen', ()) mr =>
          ∃ (mrk_r : List (BitVec 8)) (ws1_r : List (BitVec 32)) (rsz_r : BitVec 64),
            qi_c.toNat + 1 ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
            VivQueueOk c s mrk_r ws1_r qlen'.toNat ∧
            VivClosedOk s implied ws1_r ws2_b (qi_c.toNat + 1) qlen'.toNat olen_c.toNat taut_c ∧
            VivOutOk s implied ws1_r ws2_b (qi_c.toNat + 1) olen_c.toNat taut_c ∧
            VivSeedOk s cref implied ws1_r ws2_b qlen'.toNat olen_c.toNat taut_c ∧
            (implied ≠ 0xFFFFFFFF#32 →
              (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_r.take qlen'.toNat).map BitVec.toNat) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_r }
              scratch := { s.scratch with
                work_stk1 := ws1_r, work_stk2 := ws2_b, res_sz := rsz_r } } ⋆ R) mr)
        (fun _ (qlen', ()) mr ⟨mrk_r, ws1_r, rsz_r, hq1_r, hql_r, hqr, hcr, hor, hsdr,
            hsdir, hmr⟩ => by
          fv_steps; exact hJn (qlen', olen_c, taut_c, ()) mr
            ⟨mrk_r, ws1_r, ws2_b, rsz_r, hws2_b, hq1_r, hql_r, hqr, hcr, hor, hsdr,
             hsdir, hmr⟩)
        (fun Jr hJr => ?_)
      fv_to_grp
      · have hbin : (rsn_bv &&& 0x80000000#32) ≠ 0#32 := by c0_bound
        have hri := hw.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
        rw [htrl0', hrsn_get, ite_eq_left hbin] at hri
        obtain ⟨hot_lt, _, m_bin, hm_lt_bin, hmeq_bin, _⟩ := hri
        let ov_bv := (rsn_bv &&& 0x7FFFFFFF#32) >>> 1#32
        have hov_val : ov_bv.toNat = (rsn_bv &&& 0x7FFFFFFF#32).toNat / 2 :=
          bv32_lshr1_toNat _
        have hov_cv : ov_bv.toNat < s.core.cur_vars := by rw [hov_val]; omega
        have hov_trl : ∃ m < s.core.trail_end,
            (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat :=
          ⟨m_bin, by omega, by rw [hmeq_bin, fullInv_var_xor1, hov_val]⟩
        refine wp_join_group (ts := [i64])
          (fun (qlen', ()) mbin =>
            ∃ (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)),
              qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
              (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) ∧
              VivQueueOk c s mrk_n ws1_n qlen'.toNat ∧
              ((s.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
                ov_bv.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_n }
                scratch := { s.scratch with
                  work_stk1 := ws1_n, work_stk2 := ws2_b, res_sz := rsz_b } } ⋆ R) mbin)
          (fun _ (qlen', ()) mbin ⟨mrk_n, ws1_n, hq_le, hql_n, heq_n, hqn, hcov_b, hmbin⟩ => by
            fv_steps
            have hws1_n_len : ws1_n.length = 2 * c.max_vars := hqn.2.1
            have heq_qi : ws1_n[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_n qi_c.toNat hqi_lt
            have htrl0_n : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
                (ws1_n[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
            have hcb1 := vivClosed_mono_q hcb (by omega) hq_le (by have := hqb.2.1; omega)
              (by omega) heq_n
            have hcb2 := vivClosed_step_bin hcb1 hw.trail_vars_nodup hidx0 htrl0_n
              (by rw [heq_qi, hrsn_get]; exact hrsn_ne)
              (by rw [heq_qi, hrsn_get]; exact hbin)
              (by rw [heq_qi, hrsn_get, ← hov_val]; exact hcov_b)
            have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
              (by have := hqb.2.1; omega) (by omega) heq_n
            have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega) (by omega)
              (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
            have hsd1 := vivSeed_mono_q hsdb hq_le (by omega) (by have := hqb.2.1; omega) heq_n
            have hsdi1 : implied ≠ 0xFFFFFFFF#32 →
                (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat := fun hne =>
              (hsdi_b hne).elim Or.inl fun hm' => Or.inr (by
                obtain ⟨j, hj, hjeq⟩ :=
                  (mem_map_take_iff (by have := hqb.2.1; omega)).mp hm'
                exact (mem_map_take_iff (by omega)).mpr ⟨j, by omega, by rw [heq_n j hj, hjeq]⟩)
            exact hJr (qlen', ()) mbin
              ⟨mrk_n, ws1_n, rsz_b, by omega, hql_n, hqn, hcb2, hob2, hsd1, hsdi1, hmbin⟩)
          (fun Jbin hJbin => deduce_push_wp Γ hsp hw hqb hws2_b hov_cv hov_trl hmb
            fun qlen' mrk_n ws1_n mbin hq_le hql_n heq_n hqn hcov_b hmbin =>
              hJbin (qlen', ()) mbin ⟨mrk_n, ws1_n, hq_le, hql_n, heq_n, hqn, hcov_b, hmbin⟩)
      · have hlg : (rsn_bv &&& 0x80000000#32) = 0#32 := by c0_bound
        have hri := hw.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
        rw [htrl0', hrsn_get, ite_eq_right (by simp [hlg])] at hri
        obtain ⟨href_r, hng_r, hlits_r⟩ := hri
        have hv_get : v_bv = ws1_b[qi_c.toNat]?.getD 0#32 := by
          dsimp only [v_bv]; rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
        refine wp_join_group (ts := [i64])
          (fun (qlen', ()) mlg =>
            ∃ (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) (rsz_n : BitVec 64),
              qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
              (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) ∧
              VivQueueOk c s mrk_n ws1_n qlen'.toNat ∧
              (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
                (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_n }
                scratch := { s.scratch with
                  work_stk1 := ws1_n, work_stk2 := ws2_b, res_sz := rsz_n } } ⋆ R) mlg)
          (fun _ (qlen', ()) mlg ⟨mrk_n, ws1_n, rsz_n, hq_le, hql_n, heq_n, hqn, hcov_l,
              hmlg⟩ => by
            fv_steps
            have hws1_n_len : ws1_n.length = 2 * c.max_vars := hqn.2.1
            have heq_qi : ws1_n[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_n qi_c.toNat hqi_lt
            have htrl0_n : (s.core.trl[idx0]?.getD 0#32).toNat / 2 =
                (ws1_n[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
            have hcb1 := vivClosed_mono_q hcb (by omega) hq_le (by have := hqb.2.1; omega)
              (by omega) heq_n
            have hcb2 := vivClosed_step_large hcb1 hw.trail_vars_nodup hidx0 htrl0_n
              (by rw [heq_qi, hrsn_get]; exact hrsn_ne) (by rw [heq_qi, hrsn_get]; exact hlg)
              (by rw [heq_qi, hrsn_get, ← hv_get]; exact hcov_l) (by
                rw [heq_qi, hrsn_get]; intro q hq
                exact (hlits_r q hq).imp id fun ⟨m, hm', heq, _⟩ => ⟨m, hm', heq⟩)
            have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
              (by have := hqb.2.1; omega) (by omega) heq_n
            have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega) (by omega)
              (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
            have hsd1 := vivSeed_mono_q hsdb hq_le (by omega) (by have := hqb.2.1; omega) heq_n
            have hsdi1 : implied ≠ 0xFFFFFFFF#32 →
                (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat := fun hne =>
              (hsdi_b hne).elim Or.inl fun hm' => Or.inr (by
                obtain ⟨j, hj, hjeq⟩ :=
                  (mem_map_take_iff (by have := hqb.2.1; omega)).mp hm'
                exact (mem_map_take_iff (by omega)).mpr ⟨j, by omega, by rw [heq_n j hj, hjeq]⟩)
            exact hJr (qlen', ()) mlg
              ⟨mrk_n, ws1_n, rsz_n, by omega, hql_n, hqn, hcb2, hob2, hsd1, hsdi1, hmlg⟩)
          (fun Jlg hJlg => by
            have hv_set64 : ((ws1_b[qi_c.toNat]'hqi_ws1).setWidth 64).toNat = v_bv.toNat := by
              dsimp only [v_bv]; bv_omega
            have hrsn_ld :
                s.core.rsns[((ws1_b[qi_c.toNat]'hqi_ws1).setWidth 64).toNat]'(by
                  rw [hrsns_len, hv_set64]; omega) = rsn_bv := by
              dsimp only [rsn_bv]; simp only [hv_set64]
            exact deduce_large_rsn_wp Γ hsp hw hqb hws2_b (by rw [hrsn_ld]; exact href_r)
              (by rw [hrsn_ld]; exact hng_r) hidx0 htrl0
              (by
                rw [hrsn_ld]
                exact fun q hq => (hlits_r q hq).imp id fun ⟨m, hm', heq, hle⟩ =>
                  ⟨m, hm', heq, by rwa [htrl0']⟩)
              hmb
              fun qlen' mrk_n ws1_n rsz_n mlg hq_le hql_n heq_n hqn hcov_l hmlg => by
                rw [hrsn_ld] at hcov_l
                exact hJlg (qlen', ()) mlg
                  ⟨mrk_n, ws1_n, rsz_n, hq_le, hql_n, heq_n, hqn, hcov_l, hmlg⟩)
  · have hqi_eq : qi_c.toNat = qlen_c.toNat := by c0_bound
    clear hc ihb Jb
    exact deduce_clear_wp Γ hsp hw href hng hqb hws2_b hmb fun ret mrk_c mc hsp' hw' htaut_eq
        hf_eq hmc => by
      by_cases ht : taut_c
      · subst ht
        have hsz_le := fullArenaClauseSize_le_maxVars hsp hw href hng
        exact hQ ret mrk_c ws1_b ws2_b rsz_b mc hsp' hw' (by rw [htaut_eq rfl]; exact hsz_le)
          (fun hlt => by rw [htaut_eq rfl] at hlt; omega) hmc
      · simp only [Bool.not_eq_true] at ht; subst ht
        have hret := hf_eq rfl; subst ret
        have hcb' : VivClosedOk s implied ws1_b ws2_b qlen_c.toNat qlen_c.toNat olen_c.toNat
            false := by simpa only [hqi_eq] using hcb
        have hob' := hob rfl; rw [hqi_eq] at hob'
        have hent_out :=
          deduce_phase2_sound hw hqb hcv_le href hng hcb' hsdb himp hconfl hsdi_b
        exact hQ olen_c mrk_c ws1_b ws2_b rsz_b mc hsp' hw' (by have := hob'.1; omega)
          (fun _ => ⟨hob'.2.1,
            by simpa only [List.map_map, Function.comp_def] using hob'.2.2.1, hent_out⟩)
          hmc

private abbrev deducePhase1LoopExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref src_cr : Val i32) (Jsc : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_7 =>
  fvOp32 (OpCode.cmp CmpOp.ule i64 Ty.bool (by decide)) (Arg.var p.fst, Arg.var ld_7, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun Js_rs => Blocks.cons (fun (_ : Tup Val []) =>
      fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
      fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld_8 =>
      Expr.group (sig := [[i64, i32]]) (fun Js_i => Blocks.cons (fun pi =>
        fvOp32 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var pi.snd.fst, Arg.var ld_8, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
           fvOp32 (OpCode.zext 32 64) (Arg.var pi.snd.fst, ()) fun pz =>
           fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
           fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld =>
           fvOp32 (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p23 =>
           Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p24 =>
             fvOp32 (OpCode.add i32) (Arg.var pi.snd.fst, Arg.imm 1, ()) fun p1 =>
             Expr.jump Js_i.fst (Arg.var p24.fst, Arg.var p1.fst, ())) Blocks.nil) fun Js_in =>
           deducePushExpr pVars pMark pLevel pWs1 p23.fst pi.fst Js_in.fst)
          (Expr.jump Jsc (Arg.var pi.fst, ()))) Blocks.nil)
        fun Js_init => Expr.jump Js_init.fst (Arg.imm 0, Arg.imm 0, ())) Blocks.nil)
      fun Js_rs_c =>
      fvOp32 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
        (Arg.var src_cr, Arg.var cref, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
         fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
         fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
         Expr.load i32 (Arg.var p.fst) fun ld =>
         fvOp32 (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
         fvOp32 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
           (Arg.var p.fst, Arg.imm 0, ()) fun p =>
         Expr.jnz (Arg.var p.fst)
           (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
            Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.jump Js_rs_c.fst ()))
           (Expr.jump Js_rs_c.fst ()))
        (Expr.jump Js_rs_c.fst ()))
    (Expr.jump Jsc (Arg.imm 0, ()))

private theorem deduce_phase1_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {cref src_cr : Val i32} {m : Mem 64} {Q : Post [i32]} {X : XPost} {Jsc : Cont [i64]}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hsrc_ref : src_cr.toNat ∈ fullArenaClauseRefs s)
    (hsrc_ng : fullArenaClauseGarb s src_cr.toNat = false)
    (hfal_src : ∀ l ∈ fullArenaClauseLits s src_cr.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hm : (FullMem c { s with scratch := { s.scratch with res_sz := 0#64 } } ⋆ R) m)
    (hJsc : ∀ (qlen_v : Val i64) (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
        (rsz1 : BitVec 64) m2,
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s mrk1 ws1_1 qlen_v.toNat →
      (∀ l ∈ fullArenaClauseLits s src_cr.toNat,
        (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
        l / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk1 }
        scratch := { s.scratch with work_stk1 := ws1_1, res_sz := rsz1 } } ⋆ R) m2 →
      Jsc (qlen_v, ()) m2) :
    wp Γ Q X (deducePhase1LoopExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref src_cr Jsc) m := by
  have hcl := hsp.1.lengths.core_ok; have hscl := hsp.1.lengths.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have htrl_len := hcl.trl_len; have hlvl_len := hcl.lvl_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  have hsrc_wf := hw.arena.refs_wf src_cr.toNat hsrc_ref
  have hsrc_bd : src_cr.toNat + 3 + fullArenaClauseSizeCore s.core src_cr.toNat ≤
      s.core.arena.length := by omega
  dsimp only [deducePhase1LoopExpr, fvOp32]
  fv_to_grp
  · have hsrc2 : (src_cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
    let csz_bv := s.core.arena[(src_cr.setWidth 64 + 2#64).toNat]'hsrc2
    have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core src_cr.toNat := by
      unfold fullArenaClauseSizeCore
      have hsrc2_eq : (src_cr.setWidth 64 + 2#64).toNat = src_cr.toNat + 2 := by bv_omega
      simp only [csz_bv, hsrc2_eq,
        List.getElem?_eq_getElem (by omega : src_cr.toNat + 2 < s.core.arena.length),
        Option.getD_some]
    fv_to_grp
    refine wp_join_group
      (fun (_ : Tup Val []) mrs => ∃ rsz1 : BitVec 64,
        (FullMem c { s with scratch := { s.scratch with res_sz := rsz1 } } ⋆ R) mrs)
      (fun _ _ mrs ⟨rsz1, hmrs⟩ => by
        fv_to_grp
        refine wp_loop_inv (ts := [i64, i32])
          (fun (qlen_i, i_c, ()) mi =>
            ∃ (mrk_i : List (BitVec 8)) (ws1_i : List (BitVec 32)),
              i_c.toNat ≤ csz_bv.toNat ∧ qlen_i.toNat ≤ s.core.cur_vars ∧
              VivQueueOk c s mrk_i ws1_i qlen_i.toNat ∧
              (∀ t < i_c.toNat,
                let l := (s.core.arena[src_cr.toNat + 3 + t]?.getD 0#32).toNat
                (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
                l / 2 ∈ (ws1_i.take qlen_i.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_i }
                scratch := { s.scratch with work_stk1 := ws1_i, res_sz := rsz1 } } ⋆ R) mi)
          (fun (_, i_c, ()) _ => csz_bv.toNat - i_c.toNat)
          (fun Ji hJi => by
            fv_steps; exact hJi (0#64, 0#32, ()) mrs
              ⟨s.core.mrk, s.scratch.work_stk1, by simp, Nat.zero_le _, hq0,
               fun _ ht => by simp at ht, hmrs⟩)
          (fun Ji (qlen_i, i_c, ()) mi
              ⟨mrk_i, ws1_i, hi_le, hql_i, hqi_ok, hcov_i, hmi⟩ ihi => ?_)
        fv_while
        · have hi_lt : i_c.toNat < csz_bv.toNat := by c0_bound
          have hi_bd : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat =
              src_cr.toNat + 3 + i_c.toNat := by bv_omega
          have hi_ar : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat <
              s.core.arena.length := by rw [hi_bd]; omega
          let l_bv := s.core.arena[(src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat]'hi_ar
          have hl_eq : l_bv = s.core.arena[src_cr.toNat + 3 + i_c.toNat]'(by omega) := by
            dsimp only [l_bv]; simp only [hi_bd]
          have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s src_cr.toNat :=
            (mem_fullArenaClauseLitsCore_iff hsrc_bd).mpr
              ⟨i_c.toNat, by rw [← hcsz_eq]; exact hi_lt, congrArg BitVec.toNat hl_eq.symm⟩
          have hl_lt : l_bv.toNat < 2 * s.core.cur_vars :=
            hw.arena.lits_lt _ hsrc_ref hsrc_ng _ hl_mem
          have hl_fal : s.core.vals[l_bv.toNat]?.getD 0#8 = 0xFF#8 := hfal_src _ hl_mem
          obtain ⟨idx_l, hidx_l, heq_l⟩ := (hw.vals_false_iff _ hl_lt).mp hl_fal
          let lv_bv := l_bv >>> 1#32
          have hlv_val : lv_bv.toNat = l_bv.toNat / 2 := bv32_lshr1_toNat _
          have hlv_cv : lv_bv.toNat < s.core.cur_vars := by rw [hlv_val]; omega
          have hlv_trl : ∃ idx < s.core.trail_end,
              (s.core.trl[idx]?.getD 0#32).toNat / 2 = lv_bv.toNat :=
            ⟨idx_l, hidx_l, by rw [heq_l, fullInv_var_xor1, hlv_val]⟩
          have hi1 : (i_c + 1#32).toNat = i_c.toNat + 1 := by bv_omega
          fv_to_grp
          refine wp_join_group (ts := [i64])
            (fun (qlen_i', ()) mo =>
              ∃ (mrk_o : List (BitVec 8)) (ws1_o : List (BitVec 32)),
                qlen_i.toNat ≤ qlen_i'.toNat ∧ qlen_i'.toNat ≤ s.core.cur_vars ∧
                (∀ k < qlen_i.toNat, ws1_o[k]? = ws1_i[k]?) ∧
                VivQueueOk c s mrk_o ws1_o qlen_i'.toNat ∧
                ((s.core.lvl[lv_bv.toNat]?.getD 0#32).toNat = 0 ∨
                  lv_bv.toNat ∈ (ws1_o.take qlen_i'.toNat).map BitVec.toNat) ∧
                (FullMem c { s with
                  core := { s.core with mrk := mrk_o }
                  scratch := { s.scratch with work_stk1 := ws1_o, res_sz := rsz1 } } ⋆ R) mo)
            (fun _ (qlen_i', ()) mo ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩ => by
              fv_steps
              have hws1_o_len : ws1_o.length = 2 * c.max_vars := hqo.2.1
              refine ihi (qlen_i', i_c + 1#32, ()) mo (by dsimp only; omega)
                ⟨mrk_o, ws1_o, by omega, hql_o, hqo, fun t ht => ?_, hmo⟩
              rcases (by omega : t < i_c.toNat ∨ t = i_c.toNat) with ht' | rfl
              · refine (hcov_i t ht').elim Or.inl fun hm' => Or.inr ?_
                obtain ⟨k, hk, hkeq⟩ :=
                  (mem_map_take_iff (by have := hqi_ok.2.1; omega)).mp hm'
                exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq_o k hk, hkeq]⟩
              · have hleq :
                    (s.core.arena[src_cr.toNat + 3 + i_c.toNat]?.getD 0#32).toNat / 2 =
                      lv_bv.toNat := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq, hlv_val]
                dsimp only; rw [hleq]; exact hcov_lv)
            (fun Jo hJo => deduce_push_wp Γ hsp hw hqi_ok hws2_len hlv_cv hlv_trl hmi
              fun qlen' mrk_o ws1_o mo hq_io hql_o heq_o hqo hcov_lv hmo =>
                hJo (qlen', ()) mo ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩)
        · have hge_csz : csz_bv.toNat ≤ i_c.toNat := by dsimp only [csz_bv]; c0_bound
          have hi_eq : i_c.toNat = csz_bv.toNat := by omega
          exact hJsc qlen_i mrk_i ws1_i rsz1 mi hql_i hqi_ok
            (fun l hl => by
              obtain ⟨t, ht, hlt⟩ := (mem_fullArenaClauseLitsCore_iff hsrc_bd).mp hl
              rw [← hcsz_eq] at ht; have hc' := hcov_i t (by omega)
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hlt] at hc')
            hmi)
      (fun Jrs hJrs => by
        fv_steps
        · exact hJrs () _ ⟨1#64, hm⟩
        · exact hJrs () _ ⟨0#64, hm⟩
        · exact hJrs () _ ⟨0#64, hm⟩)

/-! ## 4. Parametric `Func.wp` proof for `full_viv_deduce` -/

theorem full_viv_deduce_wp (Γ : Env) :
    ∀ args m Q X, fullVivDeduceSpec args m Q X → Func.wp Γ full_viv_deduce_body args m Q X := by
  rintro ⟨h, cref, implied, out_ptr, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hw, href, hng, hconfl, himp, hm, hQ⟩
  have hcl := hsp.1.lengths.core_ok; have hscl := hsp.1.lengths.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have halen_le := hcl.arena_len_le
  have hmrk_len := hcl.mrk_len; have hlvl_len := hcl.lvl_len
  have htrl_len := hcl.trl_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  have hcref_wf := hw.arena.refs_wf cref.toNat href
  have hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0 :=
    ⟨hmrk_len, hws1_len, Nat.zero_le _, fun _ h => (by cases h), by simp,
     fun _ h => (by cases h),
     fun v hv => ⟨fun h => (by rw [hsp.2.1.1 v (by omega)] at h; cases h), fun h => (by simp at h)⟩,
     fun v hv => Or.inl (hsp.2.1.1 v (by omega)), fun v _ hv => hsp.2.1.1 v hv⟩
  fv_to_grp
  refine wp_join_group (ts := [i64, i32])
    (fun (qlen_v, olen_v, ()) mp =>
      ∃ (mrk1 : List (BitVec 8)) (ws1_1 ws2_1 : List (BitVec 32)) (rsz1 : BitVec 64),
      ws2_1.length = 2 * c.max_vars ∧ qlen_v.toNat ≤ s.core.cur_vars ∧
      VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
      VivOutOk s implied ws1_1 ws2_1 0 olen_v.toNat false ∧
      VivSeedOk s cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false ∧
      (implied ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
        implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
      (FullMem c { s with
        core := { s.core with mrk := mrk1 }
        scratch := { s.scratch with
          work_stk1 := ws1_1, work_stk2 := ws2_1, res_sz := rsz1 } } ⋆ R) mp)
    (fun _ (qlen_v, olen_v, ()) mp ⟨mrk1, ws1_1, ws2_1, rsz1, hws2_1, hql1, hq1, ho1, hsd1,
        hsd_imp1, hmp⟩ =>
      deduce_phase2_wp Γ hsp hw href hng hconfl himp hws2_1 hql1 hq1 ho1 hsd1 hsd_imp1 hmp hQ)
    (fun Js hJs => ?_)
  fv_to_grp
  · have himp_ne : implied ≠ 0xFFFFFFFF#32 := by c0_bound
    obtain ⟨himp_lt, himp_v1⟩ := himp himp_ne
    have hcv_pos : 0 < s.core.cur_vars := by omega
    have hws2_pos : 0 < s.scratch.work_stk2.length := by omega
    have hiv_lt : (implied >>> 1#32).toNat < s.core.cur_vars := by
      rw [bv32_lshr1_toNat]; omega
    fv_to_grp
    refine wp_join_group (ts := [i64])
      (fun (qlen_v, ()) m1 => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32)),
        qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
        ((s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
        (FullMem c { s with
          core := { s.core with mrk := mrk1 }
          scratch := { s.scratch with work_stk1 := ws1_1, res_sz := 0#64 } } ⋆ R) m1)
      (fun _ (qlen_v, ()) m1 ⟨mrk1, ws1_1, hql1, hq1, hsdi1, hm1⟩ => by
        fv_steps
        have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
        have hws2' : (s.scratch.work_stk2.set 0 implied).length = 2 * c.max_vars := by
          simp [hws2_len]
        refine hJs (qlen_v, 1#32, ()) _
          ⟨mrk1, ws1_1, s.scratch.work_stk2.set 0 implied, 0#64, hws2', hql1, hq1,
           fun _ => ⟨by rw [h1_32]; omega, fun i hi => by
               rw [h1_32] at hi
               have : i = 0 := by omega
               subst this; rw [List.getElem?_set_self hws2_pos, Option.getD_some]; exact himp_lt,
             by rw [h1_32, show (s.scratch.work_stk2.set 0 implied).take 1 = [implied] by
                 cases h : s.scratch.work_stk2 with
                 | nil => simp [h] at hws2_pos
                 | cons _ _ => rfl]
                simp,
             fun i hi => by
               rw [h1_32] at hi
               have : i = 0 := by omega
               subst this; rw [List.getElem?_set_self hws2_pos, Option.getD_some]
               exact Or.inl ⟨himp_ne, rfl, rfl⟩,
             fun _ => ⟨by rw [h1_32]; decide, List.getElem?_set_self hws2_pos⟩,
             fun j hj => by simp at hj⟩,
           fun _ => by
             rw [h1_32]
             simp only [himp_ne, ne_eq, not_false_eq_true, ↓reduceIte]
             exact (mem_map_take_iff (by simp [hws2_len]; omega)).mpr
               ⟨0, by omega, by rw [List.getElem?_set_self hws2_pos, Option.getD_some]⟩,
           fun _ => hsdi1, by assumption⟩)
      (fun J1 hJ1 => ?_)
    have hiv_lvl : (implied >>> 1#32).toNat < s.core.lvl.length := by omega
    have hiv_mrk : (implied >>> 1#32).toNat < s.core.mrk.length := by omega
    have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
    have h0_64 : (0#64 : BitVec 64).toNat = 0 := rfl
    fv_steps
    · have hlvl_pos : 0 < (s.core.lvl[(implied >>> 1#32).toNat]'hiv_lvl).toNat := by c0_bound
      have hlvl_pos' : 0 < (s.core.lvl[(implied >>> 1#32).toNat]?.getD 0#32).toNat := by
        rwa [List.getElem?_eq_getElem hiv_lvl, Option.getD_some]
      have hm0' : s.core.mrk[(implied >>> 1#32).toNat]?.getD 0#8 = 0#8 := hsp.2.1.1 _ (by omega)
      obtain ⟨idx_i, hidx_i, heq_i⟩ := (hw.vals_true_iff implied.toNat himp_lt).mp himp_v1
      have htrl_i : ∃ idx < s.core.trail_end,
          (s.core.trl[idx]?.getD 0#32).toNat / 2 = (implied >>> 1#32).toNat :=
        ⟨idx_i, hidx_i, by rw [heq_i, bv32_lshr1_toNat]⟩
      obtain ⟨_, hq1, _, _⟩ := push_queue_step hq0 hcv_le hiv_lt hlvl_pos' hm0' htrl_i
      refine hJ1 (1#64, ()) _ ⟨_, _, by rw [h1_64]; exact hcv_pos,
        (by rw [h1_64]; exact hq1), Or.inr ?_, hm⟩
      rw [h1_64]
      exact (mem_map_take_iff (by simp [hws1_len]; omega)).mpr
        ⟨0, by omega, by
          rw [List.getElem?_set_self (by omega)]
          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩
    · have hlvl0 : (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 := by
        have hc0 : ¬ 0 < (s.core.lvl[implied.toNat / 2]'(by
            rw [← bv32_lshr1_toNat implied]; exact hiv_lvl)).toNat := by simpa using hc
        rw [List.getElem?_eq_getElem (by rw [← bv32_lshr1_toNat implied]; exact hiv_lvl),
          Option.getD_some]
        omega
      exact hJ1 (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _,
        (by rw [h0_64]; exact hq0), Or.inl hlvl0, hm⟩
  · have himp_eq : implied = 0xFFFFFFFF#32 := by c0_bound
    refine wp_join_group (ts := [i32])
      (fun (src_cr, ()) m1 => m1 = m ∧
        src_cr.toNat = (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∧
        src_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s src_cr.toNat = false)
      (fun _ (src_cr, ()) m1 ⟨hm1, hsrc_eq, hsrc_ref, hsrc_ng⟩ => by
        subst hm1
        fv_to_grp
        refine wp_join_group (ts := [i64])
          (fun (qlen_v, ()) m2 => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
              (rsz1 : BitVec 64),
            qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
            VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk1 }
              scratch := { s.scratch with
                work_stk1 := ws1_1, res_sz := rsz1 } } ⋆ R) m2)
          (fun _ (qlen_v, ()) m2 ⟨mrk1, ws1_1, rsz1, hql1, hq1, hsd1, hm2⟩ => by
            fv_steps
            have h0_32 : (0#32 : BitVec 32).toNat = 0 := rfl
            exact hJs (qlen_v, 0#32, ()) m2 ⟨mrk1, ws1_1, s.scratch.work_stk2, rsz1, hws2_len,
              hql1, hq1, fun _ => by
                rw [h0_32]
                exact ⟨Nat.zero_le _, fun _ h => by omega, by simp, fun _ h => by omega,
                  fun hne => absurd himp_eq hne, fun _ h => by omega⟩,
              by rw [h0_32]; exact hsd1, fun hne => absurd himp_eq hne, hm2⟩)
          (fun Jq hJq => ?_)
        fv_to_grp
        · have hct1 : s.core.confl_type = 1#64 := by c0_bound
          rcases hconfl himp_eq with
            (⟨_, ha_lt, hb_lt, hent_ab, hva, hvb⟩ | ⟨hct2, _⟩) | ⟨hct0, _⟩
          · obtain ⟨idx_a, hidx_a, heq_a⟩ := (hw.vals_false_iff _ ha_lt).mp hva
            obtain ⟨idx_b, hidx_b, heq_b⟩ := (hw.vals_false_iff _ hb_lt).mp hvb
            let a_bv := s.core.confl_lit0.truncate 32
            let b_bv := s.core.confl_lit1.truncate 32
            have ha_cv : (a_bv >>> 1#32).toNat < s.core.cur_vars := by
              rw [bv32_lshr1_toNat]; dsimp only [a_bv]; omega
            have hb_cv : (b_bv >>> 1#32).toNat < s.core.cur_vars := by
              rw [bv32_lshr1_toNat]; dsimp only [b_bv]; omega
            have ha_trl : ∃ idx < s.core.trail_end,
                (s.core.trl[idx]?.getD 0#32).toNat / 2 = (a_bv >>> 1#32).toNat :=
              ⟨idx_a, hidx_a, by rw [heq_a, fullInv_var_xor1, bv32_lshr1_toNat]⟩
            have hb_trl : ∃ idx < s.core.trail_end,
                (s.core.trl[idx]?.getD 0#32).toNat / 2 = (b_bv >>> 1#32).toNat :=
              ⟨idx_b, hidx_b, by rw [heq_b, fullInv_var_xor1, bv32_lshr1_toNat]⟩
            fv_to_grp
            refine wp_join_group (ts := [i64])
              (fun (qlen_a, ()) ma => ∃ (mrk_a : List (BitVec 8)) (ws1_a : List (BitVec 32)),
                qlen_a.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_a ws1_a qlen_a.toNat ∧
                ((s.core.lvl[a_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
                  a_bv.toNat / 2 ∈ (ws1_a.take qlen_a.toNat).map BitVec.toNat) ∧
                (FullMem c { s with
                  core := { s.core with mrk := mrk_a }
                  scratch := { s.scratch with work_stk1 := ws1_a, res_sz := 0#64 } } ⋆ R) ma)
              (fun _ (qlen_a, ()) ma ⟨mrk_a, ws1_a, hql_a, hqa, hca, hma⟩ => by
                fv_to_grp
                refine wp_join_group (ts := [i64])
                  (fun (qlen_b, ()) mb => ∃ (mrk_b : List (BitVec 8)) (ws1_b : List (BitVec 32)),
                    qlen_b.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_b ws1_b qlen_b.toNat ∧
                    ((s.core.lvl[a_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
                      a_bv.toNat / 2 ∈ (ws1_b.take qlen_b.toNat).map BitVec.toNat) ∧
                    ((s.core.lvl[b_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
                      b_bv.toNat / 2 ∈ (ws1_b.take qlen_b.toNat).map BitVec.toNat) ∧
                    (FullMem c { s with
                      core := { s.core with mrk := mrk_b }
                      scratch := { s.scratch with work_stk1 := ws1_b, res_sz := 0#64 } } ⋆ R) mb)
                  (fun _ (qlen_b, ()) mb ⟨mrk_b, ws1_b, hql_b, hqb, hca', hcb', hmb⟩ => by
                    fv_steps; exact hJq (qlen_b, ()) mb ⟨mrk_b, ws1_b, 0#64, hql_b, hqb,
                      fun _ => by
                        simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct1]
                        exact ⟨hca', hcb'⟩, hmb⟩)
                  (fun Jb hJb => by
                    have hb_lvl : (b_bv >>> 1#32).toNat < s.core.lvl.length := by omega
                    have hb_mrk : (b_bv >>> 1#32).toNat < mrk_a.length := by rw [hqa.1]; omega
                    have hb_mod : (b_bv >>> 1#32).toNat % 2 ^ 64 = (b_bv >>> 1#32).toNat :=
                      Nat.mod_eq_of_lt (by omega)
                    have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
                    have ha_mem_upd : ∀ (ws1' : List (BitVec 32)) (q' : Nat),
                        qlen_a.toNat ≤ q' → q' ≤ ws1'.length →
                        (∀ j < qlen_a.toNat, ws1'[j]? = ws1_a[j]?) →
                        (s.core.lvl[a_bv.toNat / 2]?.getD 0#32).toNat = 0 ∨
                          a_bv.toNat / 2 ∈ (ws1'.take q').map BitVec.toNat :=
                      fun ws1' q' h1 h2 heq =>
                        hca.elim Or.inl fun hm' => Or.inr (by
                          obtain ⟨j, hj, hjeq⟩ :=
                            (mem_map_take_iff (by have := hqa.2.1; omega)).mp hm'
                          exact (mem_map_take_iff h2).mpr ⟨j, by omega, by rw [heq j hj, hjeq]⟩)
                    fv_steps
                    · have hm0 : mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk = 0#8 := by
                        have hm032 : (mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk).setWidth 32 = 0#32 := by
                          assumption
                        exact (bv8_zext32_eq0_iff _).mp hm032
                      have hm0' : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                        rwa [List.getElem?_eq_getElem hb_mrk, Option.getD_some]
                      have hlvl_pos' : 0 < (s.core.lvl[(b_bv >>> 1#32).toNat]?.getD 0#32).toNat :=
                          by
                        rw [List.getElem?_eq_getElem hb_lvl, Option.getD_some]; c0_bound
                      have hql_lt := push_queue_lt hqa hcv_le hb_cv hm0'
                      have hql_ws1 : qlen_a.toNat < ws1_a.length := by have := hqa.2.1; omega
                      have hql1 : (qlen_a + 1#64).toNat = qlen_a.toNat + 1 := by bv_omega
                      obtain ⟨_, hq_next, hpre_next, _⟩ :=
                        push_queue_step hqa hcv_le hb_cv hlvl_pos' hm0' hb_trl
                      fv_steps
                      simp only [hb_mod] at *
                      have hb_mod32 : (s.core.confl_lit1.toNat % 2 ^ 32) % 2 ^ 64 =
                          s.core.confl_lit1.toNat % 2 ^ 32 :=
                        Nat.mod_eq_of_lt (Nat.lt_trans (s.core.confl_lit1.truncate 32).isLt
                          (by decide))
                      refine hJb (qlen_a + 1#64, ()) _ ⟨_, _, by dsimp only; omega, ?_,
                        ha_mem_upd _ _ (by dsimp only; omega) (by simp [hqa.2.1]; omega) hpre_next,
                        Or.inr ?_, by assumption⟩
                      · simpa [hql1, hb_mod32, show b_bv.toNat = s.core.confl_lit1.toNat % 2 ^ 32
                          from rfl] using hq_next
                      · rw [hql1]; exact (mem_map_take_iff (by simp [hqa.2.1]; omega)).mpr
                          ⟨qlen_a.toNat, by omega, by
                            rw [List.getElem?_set_self hql_ws1]
                            simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩
                    · have hm0 : mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk = 0#8 := by
                        have hm032 : (mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk).setWidth 32 = 0#32 := by
                          assumption
                        exact (bv8_zext32_eq0_iff _).mp hm032
                      have hm0' : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                        rwa [List.getElem?_eq_getElem hb_mrk, Option.getD_some]
                      have hlvl_lt := push_queue_lt hqa hcv_le hb_cv hm0'
                      have hle : s.core.cur_vars % 2 ^ 64 ≤ qlen_a.toNat := by c0_bound
                      rw [Nat.mod_eq_of_lt hcv_64] at hle; omega
                    · have hm_ne0 : mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk ≠ 0#8 := fun h => by
                        have hne32 : (mrk_a[(b_bv >>> 1#32).toNat]'hb_mrk).setWidth 32 ≠ 0#32 := by
                          assumption
                        exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
                      have hm1 : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 1#8 := by
                        rcases hqa.2.2.2.2.2.2.2.1 (b_bv >>> 1#32).toNat hb_cv with h0 | h1
                        · rw [List.getElem?_eq_getElem hb_mrk, Option.getD_some] at h0
                          exact absurd h0 hm_ne0
                        · exact h1
                      exact hJb (qlen_a, ()) ma ⟨mrk_a, ws1_a, hql_a, hqa, hca,
                        Or.inr (by rw [← bv32_lshr1_toNat b_bv]
                                   exact (hqa.2.2.2.2.2.2.1 _ hb_cv).mp hm1), hma⟩
                    · have hlvl0 : (s.core.lvl[b_bv.toNat / 2]?.getD 0#32).toNat = 0 := by
                        have hc0 : ¬ 0 < (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
                            rw [← show (b_bv >>> 1#32).toNat = s.core.confl_lit1.toNat % 2 ^ 32 / 2
                              from bv32_lshr1_toNat _]; exact hb_lvl)).toNat := by simpa using hc
                        rw [List.getElem?_eq_getElem (by
                            rw [← bv32_lshr1_toNat b_bv]; exact hb_lvl), Option.getD_some]
                        exact Nat.eq_zero_of_not_pos hc0
                      exact hJb (qlen_a, ()) ma ⟨mrk_a, ws1_a, hql_a, hqa, hca,
                        Or.inl hlvl0, hma⟩))
              (fun Ja hJa => by
                have ha_lvl : (a_bv >>> 1#32).toNat < s.core.lvl.length := by omega
                have ha_mrk : (a_bv >>> 1#32).toNat < s.core.mrk.length := by omega
                have ha_lt_mv : (a_bv >>> 1#32).toNat < c.max_vars :=
                  Nat.lt_of_lt_of_le ha_cv hcv_le
                have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
                have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
                have h0_64 : (0#64 : BitVec 64).toNat = 0 := rfl
                fv_steps
                · have hlvl_pos' : 0 < (s.core.lvl[(a_bv >>> 1#32).toNat]?.getD 0#32).toNat := by
                    rw [List.getElem?_eq_getElem ha_lvl, Option.getD_some]; c0_bound
                  have hm0' : s.core.mrk[(a_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 :=
                    hsp.2.1.1 _ ha_lt_mv
                  obtain ⟨_, hq1, _, _⟩ := push_queue_step hq0 hcv_le ha_cv hlvl_pos' hm0' ha_trl
                  exact hJa (1#64, ()) _ ⟨_, _, (by rw [h1_64]; omega),
                    (by rw [h1_64]; exact hq1), Or.inr (by
                      rw [h1_64]; exact (mem_map_take_iff (by simp [hws1_len]; omega)).mpr
                        ⟨0, by omega, by
                          rw [List.getElem?_set_self (by omega)]
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩),
                    by assumption⟩
                · have hm0' : s.core.mrk[(a_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 :=
                    hsp.2.1.1 _ ha_lt_mv
                  rw [List.getElem?_eq_getElem ha_mrk, Option.getD_some] at hm0'
                  have h032 : (s.core.mrk[(a_bv >>> 1#32).toNat]'ha_mrk).setWidth 32 = 0#32 :=
                    (bv8_zext32_eq0_iff _).mpr hm0'
                  have hne32 : (s.core.mrk[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
                      rw [← show (a_bv >>> 1#32).toNat = s.core.confl_lit0.toNat % 2 ^ 32 / 2
                        from bv32_lshr1_toNat _]; exact ha_mrk)).setWidth 32 ≠ 0#32 := by
                    assumption
                  exact absurd h032 hne32
                · have hlvl0 : (s.core.lvl[a_bv.toNat / 2]?.getD 0#32).toNat = 0 := by
                    have hc0 : ¬ 0 < (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
                        rw [← show (a_bv >>> 1#32).toNat = s.core.confl_lit0.toNat % 2 ^ 32 / 2
                          from bv32_lshr1_toNat _]; exact ha_lvl)).toNat := by simpa using hc
                    rw [List.getElem?_eq_getElem (by
                        rw [← bv32_lshr1_toNat a_bv]; exact ha_lvl), Option.getD_some]
                    exact Nat.eq_zero_of_not_pos hc0
                  exact hJa (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _,
                    (by rw [h0_64]; exact hq0), Or.inl hlvl0, hm⟩)
          · exact absurd (hct2.symm.trans hct1) (by decide)
          · exact absurd (hct0.symm.trans hct1) (by decide)
        · have hct_ne1 : s.core.confl_type ≠ 1#64 := by c0_bound
          have hfal_src : ∀ l ∈ fullArenaClauseLits s src_cr.toNat,
              s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            rcases hconfl himp_eq with (⟨hct1, _⟩ | ⟨hct2, _, _, hf2⟩) | ⟨hct0, hf0⟩
            · exact absurd hct1 hct_ne1
            · rw [hsrc_eq]; simp [hct2]; exact hf2
            · rw [hsrc_eq]; have hne2 : s.core.confl_type ≠ 2#64 := by rw [hct0]; decide
              simp [hne2]; exact hf0
          refine wp_join_group (ts := [i64])
            (fun (qlen_v, ()) m2 => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
                (rsz1 : BitVec 64),
              qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
              (∀ l ∈ fullArenaClauseLits s src_cr.toNat,
                (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
                l / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk1 }
                scratch := { s.scratch with work_stk1 := ws1_1, res_sz := rsz1 } } ⋆ R) m2)
            (fun _ (qlen_v, ()) m2 ⟨mrk1, ws1_1, rsz1, hql1, hq1, hcov_src, hm2⟩ => by
              fv_steps; exact hJq (qlen_v, ()) m2 ⟨mrk1, ws1_1, rsz1, hql1, hq1,
                fun _ => by
                  simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct_ne1]
                  have hsrc_c : (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else
                      cref.toNat) = src_cr.toNat := hsrc_eq.symm
                  rwa [hsrc_c], hm2⟩)
            (fun Jsc hJsc => deduce_phase1_loop_wp Γ hsp hw hq0 hsrc_ref hsrc_ng hfal_src hm
              fun qlen_v mrk1 ws1_1 rsz1 m2 hql1 hq1 hcov_src hm2 =>
                hJsc (qlen_v, ()) m2 ⟨mrk1, ws1_1, rsz1, hql1, hq1, hcov_src, hm2⟩))
      (fun Jsrc hJsrc => by
        fv_steps
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

end

end LeanQbe.T.Examples.Kissat.Full
